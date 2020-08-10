import * as path from 'path'
import * as vscode from 'vscode'
import * as LanguageClient from 'vscode-languageclient'

let client: LanguageClient.LanguageClient

export function activate(context: vscode.ExtensionContext): void {

    vscode.window.showInformationMessage('crux-llvm extension activated')

    const serverModule = context.asAbsolutePath(path.join('server', 'out', 'server.js'))

    const debugOptions = {
        execArgv: [
            '--inspect=6009',
            '--nolazy',
        ]
    }

    const serverOptions = {
        run: {
            module: serverModule,
            transport: LanguageClient.TransportKind.ipc,
        },
        debug: {
            module: serverModule,
            transport: LanguageClient.TransportKind.ipc,
            options: debugOptions
        }
    }

    const clientOptions: LanguageClient.LanguageClientOptions = {
        documentSelector: [{ scheme: 'file', language: 'c' }],
        synchronize: {
            fileEvents: vscode.workspace.createFileSystemWatcher('**/*.c')
        }
    }

    client = new LanguageClient.LanguageClient(
        'crux-llvm',
        'CruxLLVM Language Server',
        serverOptions,
        clientOptions
    )

    client.start()

}

export function deactivate(): Promise<void> {
    if (!client) {
        return Promise.resolve()
    }
    return client.stop()
}