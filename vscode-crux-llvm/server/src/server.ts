import * as path from 'path'

import { debounce } from 'debounce'
import * as LanguageServer from 'vscode-languageserver'
// import { WorkDoneProgress, WorkDoneProgressCreateRequest } from 'vscode-languageserver'
import { TextDocument } from 'vscode-languageserver-textdocument'
// import { attachWorkDone, createWorkDoneProgress } from 'vscode-languageserver/lib/common/progress'
import * as LanguageServerNode from 'vscode-languageserver/node'

import * as Configuration from '@shared/configuration'
import * as Constants from '@shared/constants'
import { checkCommand, checkCommandViaPATH } from '@shared/node/check-command'
import { validateTextDocument } from '@shared/node/validate'

/** Connection to the extension front-end */

const connection: LanguageServerNode.Connection = (
    LanguageServerNode.createConnection(LanguageServerNode.ProposedFeatures.all)
)

console.log = connection.console.log.bind(connection.console)
console.error = connection.console.error.bind(connection.console)

/** Documents being watched */
const documents: LanguageServerNode.TextDocuments<TextDocument> =
    new LanguageServerNode.TextDocuments<TextDocument>({
        create(uri: string, languageId: string, version: number, content: string): TextDocument {
            return TextDocument.create(uri, languageId, version, content)
        },
        update(document: TextDocument): TextDocument {
            return document
        },
    })

// We should only tell the client that we initiated a cancellable verification
// task if it explicitly supports receiving such notifications.
// cf. https://microsoft.github.io/language-server-protocol/specifications/specification-current/#serverInitiatedProgress
let clientSupportsWorkDoneProgress = false

connection.onInitialize(
    (params: LanguageServer.InitializeParams) => {
        if (params.capabilities.window?.workDoneProgress) {
            clientSupportsWorkDoneProgress = true
        }
        return ({
            capabilities: {
                textDocumentSync: {
                    change: LanguageServerNode.TextDocumentSyncKind.Full,
                    openClose: true,
                },
            },
        } as LanguageServer.InitializeResult<void>)
    }
)

connection.onInitialized(checkConfiguration)
/**
 * Returns the actual command to use for running a given command, based on the
 * configuration.
 * @param command - Command to resolve, say `clang`
 * @param configuration - crux-llvm fragment of the user's settings.json
 * @returns Resolved command, say `/path/to/clang`
 */
// function commandFromConfiguration(command: string, configuration: any): string {
//     if (command in configuration) {
//         return configuration[command]
//     }
//     return command
// }

/**
 * Outputs a message to the user's console, if debug is set to true in their
 * configuration.  To find these messages, I have to go in the extension's
 * Output tab, and select the "Crux-LLVM Language Server" option from the
 * drop-down on the right.
 * @param str - Message to output
 */
async function debugMessage(str: string): Promise<void> {
    const configuration = await connection.workspace.getConfiguration(Constants.settingsName)
    if (configuration[Configuration.configDebug]) {
        connection.console.info(`${Constants.prefix}\n${str}`)
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
    const configuration: Configuration.Configuration = await connection.workspace.getConfiguration(Constants.settingsName)

    const check = (field: keyof Configuration.Configuration & string) => {
        const result = checkCommand(configuration, field)
        if (result.check) {
            return true
        } else {
            connection.window.showErrorMessage(result.errorMessage)
            return false
        }
    }

    const checkViaPATH = (command: string) => {
        const result = checkCommandViaPATH(configuration, command)
        if (result.check) {
            return true
        } else {
            connection.window.showErrorMessage(result.errorMessage)
            return false
        }
    }

    return (
        check(Configuration.configCruxLLVM)
        &&
        check(Configuration.configClang)
        &&
        check(Configuration.configLLVMLink)
        &&
        checkViaPATH('z3')
    )
}

async function onChangedContent(
    change: LanguageServer.TextDocumentChangeEvent<TextDocument>,
): Promise<void> {

    const configurationOK = await checkConfiguration()
    if (!configurationOK) {
        return
    }

    const progress = await connection.window.createWorkDoneProgress()

    if (clientSupportsWorkDoneProgress) {
        const filename = path.basename(change.document.uri)
        progress.begin('Crux-LLVM', 0, `Checking ${filename}`, true)
        progress.token.onCancellationRequested(() => {
            debugMessage('Cancellation has been requested, TODO')
        })
    }

    const configuration = await connection.workspace.getConfiguration(Constants.settingsName)
    const document = change.document

    // uri will look like 'file:///path/to/file.c'
    // but we need it to be '/path/to/file.c'
    const filePath = document.uri.replace('file://', '')

    await validateTextDocument(configuration, filePath, {
        onDiagnostics: (diagnostics) => {
            if (clientSupportsWorkDoneProgress) {
                progress.done()
            }
            connection.sendDiagnostics({
                uri: document.uri,
                diagnostics,
            })
        },
        onError: (e) => {
            if (clientSupportsWorkDoneProgress) {
                progress.done()
            }
            connection.window.showErrorMessage(e)
        },
        onWarning: (w) => connection.window.showWarningMessage(w),
    })

    debugMessage('Done validating')

}

documents.onDidChangeContent(debounce(onChangedContent))

documents.listen(connection)

connection.listen()
