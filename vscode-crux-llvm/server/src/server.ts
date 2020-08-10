import * as ChildProcess from 'child_process'
import { debounce } from 'debounce'
import * as fs from 'fs'
import * as LanguageServer from 'vscode-languageserver'
import * as os from 'os'
import * as path from 'path'

import * as Report from './report'

const prefix: string = '[vscode-crux-llvm]'
const settingsName: string = 'vscode-crux-llvm'

/** Promisified version of nodejs' filesystem API */
const fsPromises = fs.promises

/** Connection to the extension front-end */
const connection: LanguageServer.IConnection =
    LanguageServer.createConnection(LanguageServer.ProposedFeatures.all)

/** Documents being watched */
const documents: LanguageServer.TextDocuments<LanguageServer.TextDocument> =
    new LanguageServer.TextDocuments<LanguageServer.TextDocument>({
        create(uri: string, languageId: string, version: number, content: string): LanguageServer.TextDocument {
            return LanguageServer.TextDocument.create(uri, languageId, version, content)
        },
        update(document: LanguageServer.TextDocument): LanguageServer.TextDocument {
            return document
        },
    })

connection.onInitialize(
    () => {
        return {
            capabilities: {
                textDocumentSync: {
                    openClose: true,
                    change: LanguageServer.TextDocumentSyncKind.Full,
                },
            }
        }
    }
)

connection.onInitialized(checkConfiguration)

/**
 * Runs crux-llvm on a given text document, reporting using the diagnostics API
 * @param textDocument The text document to validate
 */
async function validateTextDocument(textDocument: LanguageServer.TextDocument): Promise<void> {

    // uri will look like 'file:///path/to/file.c'
    // but we need it to be '/path/to/file.c'
    const filePath = textDocument.uri.replace('file://', '')
    const configuration = await connection.workspace.getConfiguration('crux-llvm')
    const cruxLLVM = configuration['crux-llvm']

    // we use a temporary directory to produce the report
    const tempDir = await fsPromises.mkdtemp(path.join(os.tmpdir(), 'crux-llvm-'))
    const includeDirs = configuration['include-dirs']

    // ! Do not try to timeout this process from vscode, as it may crash the
    // ! entire IDE
    const cruxLLVMProcess = ChildProcess.execFile(
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
                CLANG: configuration.clang,
                LLVM_LINK: configuration['llvm-link'],
                PATH: configuration.path,
            },
        })

    // ! Killing crux-llvm this way may bring down vscode entirely!
    // setTimeout(() => { cruxLLVMProcess.kill() }, 1000)

    cruxLLVMProcess.on('exit', () => {
        try {
            // crux-llvm can generate huge reports, arbitrary cutoff
            const reportFile = `${tempDir}/report.json`
            const sizeInMegabytes = fs.statSync(reportFile).size / 1_000_000
            if (sizeInMegabytes > 1) {
                connection.window.showWarningMessage(`Skipping ${reportFile} as it appears to be larger than 1MB`)
                return
            }

            const contents = fs.readFileSync(reportFile)
            // ! may need to do some sanity checking here
            const report: any[] = JSON.parse(contents.toString())

            const diagnostics = report.flatMap(Report.createDiagnostic)

            connection.sendDiagnostics({ uri: textDocument.uri, diagnostics })
        }
        catch (e) {
            connection.window.showErrorMessage(`${prefix} Error processing report:\n${e}`)
        }
    })

}

/**
 * Returns the actual command to use for running a given command, based on the
 * configuration.
 * @param command Command to resolve, say `clang` 
 * @param configuration crux-llvm fragment of the user's settings.json 
 * @returns Resolved command, say `/path/to/clang`
 */
function commandFromConfiguration(command: string, configuration: any): string {
    if (command in configuration) {
        return configuration[command]
    }
    return command
}

/**
 * Outputs a message to the user's console, if debug is set to true
 * @param str Message to output
 */
async function debugMessage(str: string): Promise<void> {
    const configuration = await connection.workspace.getConfiguration('crux-llvm')
    if (configuration.debug) {
        connection.console.info(`${prefix}\n${str}`)
    }
}

/** 
 * @param configuration crux-llvm fragment of the user's settings.json
 * 
 * @param commandStr one of the command names expected as fields (see
 * vscode-crux-llvm/package.json) for an up-to-date list
 * 
 * @returns true when command can be found, false otherwise
 */
function checkCommand(configuration: any, commandStr: string): boolean {
    try {
        const output = ChildProcess.execFileSync(
            configuration[commandStr],
            ['--version'],
        )
        debugMessage(output.toString())
        return true
    }
    catch (e) { // ! e will be null
        connection.window.showErrorMessage(
            `${commandStr} could not be found.  Please set "${settingsName}.${commandStr}" correctly in your settings.json.`
        )
        return false
    }
}

/** 
 * Checks that we can access a given command using the user's settings PATH
 * @param configuration crux-llvm fragment of the user's settings.json
 * @param commandStr a verbatim command name we expect to found in PATH
 * @returns true when command can be found, false otherwise
 */
function checkCommandViaPATH(configuration: any, commandStr: string): boolean {
    try {
        const output = ChildProcess.execFileSync(
            commandStr,
            ['--version'],
            {
                env: {
                    PATH: configuration['path'],
                },
            },
        )
        debugMessage(output.toString())
        return true
    }
    catch (e) { // ! e will be null
        connection.window.showErrorMessage(
            `${commandStr} could not be found.  Please make sure that "${settingsName}.path" is a PATH containing ${commandStr} in your settings.json.`
        )
        return false
    }
}

// ? I was hoping to use `onDidChangeConfiguration` to keep track of when the
// ? user modifies their settings.json, however, in my experience, the callback
// ? does not trigger.
/**
 * Checks whether the necessary binaries are accessible
 * @returns true if all commands can be found, false otherwise
 */
async function checkConfiguration(): Promise<boolean> {
    const configuration = await connection.workspace.getConfiguration('crux-llvm')
    return (
        checkCommand(configuration, 'crux-llvm')
        &&
        checkCommand(configuration, 'clang')
        &&
        checkCommand(configuration, 'llvm-link')
        &&
        checkCommandViaPATH(configuration, 'z3')
    )
}

async function onChangedContent(change: LanguageServer.TextDocumentChangeEvent<LanguageServer.TextDocument>): Promise<void> {
    const configurationOK = await checkConfiguration()
    if (!configurationOK) {
        return
    }
    debugMessage('About to validate')
    validateTextDocument(change.document)
    debugMessage('Done validating')
}

documents.onDidChangeContent(debounce(onChangedContent))
documents.listen(connection)
connection.listen()