import * as ChildProcess from 'child_process'
import * as fs from 'fs'
import * as os from 'os'
import * as path from 'path'

import { Diagnostic } from 'vscode-languageserver'

import * as Configuration from '@shared/configuration'
import { prefix } from '@shared/constants'
import * as Report from '@shared/report'

export const websocketURL = '127.0.0.1'
export const websocketPort = 1234

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
        onExit: () => void,
        onWarning: (warning: string) => void,
    },
): Promise<ChildProcess.ChildProcessWithoutNullStreams> {

    const cruxLLVM = configuration[Configuration.ConfigurationKeys.CruxLLVM]

    // we use a temporary directory to produce the report
    const tempDir = await fsPromises.mkdtemp(path.join(os.tmpdir(), 'temp-crux-llvm-'))
    const includeDirs = configuration[Configuration.ConfigurationKeys.IncludeDirs]

    const includes = includeDirs.map(d => `--include-dirs=${d}`)

    // const cruxLLVMProcess = ChildProcess.execFile(
    const cruxLLVMProcess = ChildProcess.spawn(
        cruxLLVM,
        [
            filePath,
            '--sim-verbose=3',
            '--fail-fast',
            '--goal-timeout',
            `--ide-host=${websocketURL}`,
            `--ide-port=${websocketPort}`,
            '--no-execs',
            `--output-directory=${tempDir}`,
            '--skip-incomplete-reports',
            '--skip-success-reports',
            '--solver=z3', // yices behaves badly
            '--timeout',
        ].concat(
            includes,
        ),
        {
            cwd: tempDir,
            // creates the subprocess in its own process group, necessary
            // because crux-llvm will broadcast SIGTERM to its entire process
            // group, killing VSCode in the process!
            // cf. https://github.com/GaloisInc/crucible/issues/727
            detached: true,
            env: {
                BLDDIR: tempDir,
                CLANG: configuration[Configuration.ConfigurationKeys.Clang],
                LLVM_LINK: configuration[Configuration.ConfigurationKeys.LLVMLink],
                PATH: configuration[Configuration.ConfigurationKeys.PATH],
            },
        })

    cruxLLVMProcess.stdout.on('data', data => {
        console.log(`stdout: ${data}`)
    })

    cruxLLVMProcess.stderr.on('data', data => {
        console.log(`stderr: ${data}`)
    })

    cruxLLVMProcess.on('error', e => {
        console.log(e)
    })

    cruxLLVMProcess.on('exit', () => {

        callbacks.onExit()

        try {
            console.log(cruxLLVMProcess.exitCode)
            console.log(cruxLLVMProcess.signalCode)

            // crux-llvm can generate huge reports, arbitrary cutoff
            const reportFile = `${tempDir}/report.json`

            if (!fs.existsSync(reportFile)) {
                callbacks.onError('crux-llvm did not generate report.json. Please report.')
                return
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

    return cruxLLVMProcess

}
