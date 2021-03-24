import * as ChildProcess from 'child_process'
import * as fs from 'fs'
import * as os from 'os'
import * as path from 'path'

import { Diagnostic } from 'vscode-languageserver'

import * as Configuration from '../configuration'
import { prefix } from '../constants'
import * as Report from '../report'

/** Promisified version of nodejs' filesystem API */
const fsPromises = fs.promises

// Currently, killing a ChildProcess on the server side crashes VSCode.  So we
// keep track of the caller.
export enum CallOrigin {
    client,
    server,
}

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
    origin: CallOrigin,
): Promise<void> {

    const cruxLLVM = configuration[Configuration.configCruxLLVM]

    // we use a temporary directory to produce the report
    const tempDir = await fsPromises.mkdtemp(path.join(os.tmpdir(), 'temp-crux-llvm-'))
    const includeDirs = configuration[Configuration.configIncludeDirs]

    // console.log('Starting crux-llvm child process')

    // ! Do not try to timeout this process from vscode, as it may crash the
    // ! entire IDE
    // const cruxLLVMProcess = ChildProcess.execFile(
    const cruxLLVMProcess = ChildProcess.spawn(
        cruxLLVM,
        [
            filePath,
            '--fail-fast',
            '--goal-timeout',
            '--no-execs',
            '--skip-incomplete-reports',
            '--skip-success-reports',
            '--solver=z3', // yices behaves badly
            '--timeout',
            `--output-directory=${tempDir}`,
            `--include-dirs=${includeDirs}`,
        ],
        {
            env: {
                CLANG: configuration[Configuration.configClang],
                LLVM_LINK: configuration[Configuration.configLLVMLink],
                PATH: configuration[Configuration.configPATH],
            },
        })

    // Do **not** kill if the CallOrigin is 'server', it crashes VSCode!
    if (origin === CallOrigin.client) {
        setTimeout(() => { cruxLLVMProcess.kill() }, 10_000)
    }

    // cruxLLVMProcess.stdout?.on('data', m => {
    //     console.log(m)
    // })

    cruxLLVMProcess.on('exit', () => {
        try {
            // crux-llvm can generate huge reports, arbitrary cutoff
            const reportFile = `${tempDir}/report.json`
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
