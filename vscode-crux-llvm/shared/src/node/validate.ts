import * as ChildProcess from 'child_process'
import * as fs from 'fs'
import * as http from 'http'
import * as os from 'os'
import * as path from 'path'

import { Diagnostic } from 'vscode-languageserver'
import * as ws from 'websocket'

import * as Configuration from '../configuration'
import { prefix } from '../constants'
import * as Report from '../report'

/** Promisified version of nodejs' filesystem API */
const fsPromises = fs.promises

/**
 * Runs crux-llvm on a given text document, reporting using the diagnostics API
 * @param textDocument - The text document to validate
 */
export async function validateTextDocument(
    configuration: Configuration.Configuration,
    filePath: string,
    callbacks: {
        onDiagnostics: (diagnostic: Diagnostic[]) => void,
        onError: (error: string) => void,
        onWarning: (warning: string) => void,
    },
): Promise<void> {

    const cruxLLVM = configuration[Configuration.configCruxLLVM]

    // we use a temporary directory to produce the report
    const tempDir = await fsPromises.mkdtemp(path.join(os.tmpdir(), 'temp-crux-llvm-'))
    const includeDirs = configuration[Configuration.configIncludeDirs]

    const httpServer = http.createServer((req, rsp) => {
        console.log(req, rsp)
        rsp.end()
    })
    httpServer.listen(1234, () => {
        console.log('HTTP server listening')
    })

    const server = new ws.server({
        httpServer,
    })

    server.on('request', req => {
        const connection = req.accept()

        console.log('HTTP connection accepted')

        connection.on('message', msg => {
            if (msg.type === 'utf8') {
                console.log(msg.utf8Data)
            }
        })
    })

    // const server = ws.createWebSocketStream(
    //     new ws('ws://127.0.0.1:12342'),
    // )
    // server.on('message', m => console.log(m))

    // const ws = new WebSocket('ws://localhost:1234')
    // ws.addEventListener('message', m => {
    //     console.log(m)
    // })

    // console.log('Starting crux-llvm child process')

    // const cruxLLVMProcess = ChildProcess.execFile(
    const cruxLLVMProcess = ChildProcess.spawn(
        cruxLLVM,
        [
            filePath,
            '--sim-verbose=3',
            '--fail-fast',
            '--goal-timeout',
            '--ide-host=127.0.0.1',
            '--ide-port=1234',
            `--include-dirs=${includeDirs}`,
            '--no-execs',
            `--output-directory=${tempDir}`,
            '--skip-incomplete-reports',
            '--skip-success-reports',
            '--solver=z3', // yices behaves badly
            '--timeout',
        ],
        {
            cwd: tempDir,
            // creates the subprocess in its own process group, necessary
            // because crux-llvm will broadcast SIGTERM to its entire process
            // group, killing VSCode in the process!
            // cf. https://github.com/GaloisInc/crucible/issues/727
            detached: true,
            env: {
                BLDDIR: tempDir,
                CLANG: configuration[Configuration.configClang],
                LLVM_LINK: configuration[Configuration.configLLVMLink],
                PATH: configuration[Configuration.configPATH],
            },
        })

    cruxLLVMProcess.stderr?.on('data', m => {
        callbacks.onError(m.toString())
    })

    cruxLLVMProcess.stdout?.on('data', m => {
        console.log(m.toString())
    })

    cruxLLVMProcess.on('exit', () => {
        try {
            // crux-llvm can generate huge reports, arbitrary cutoff
            const reportFile = `${tempDir}/report.json`

            if (!fs.existsSync(reportFile)) {
                callbacks.onError('crux-llvm did not generate report.json. Please report.')
            }

            const sizeInMegabytes = fs.statSync(reportFile).size / 1_000_000
            if (sizeInMegabytes > 1) {
                callbacks.onWarning(`Skipping ${reportFile} as it appears to be larger than 1MB`)
                return
            }

            const contents = fs.readFileSync(reportFile)
            // ! may need to do some sanity checking here
            const report: Report.MainDiagnostic[] = JSON.parse(contents.toString())

            const diagnostics = report.flatMap(Report.createDiagnostic)

            callbacks.onDiagnostics(diagnostics)
        } catch (e) {
            callbacks.onError(`${prefix} Error processing report:\n${e}`)
        }
    })

}
