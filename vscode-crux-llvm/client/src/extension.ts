import * as path from 'path'

import * as vscode from 'vscode'
import * as lc from 'vscode-languageclient/node'

import { CruxLLVMViewProvider } from './crux-llvm-view-provider'


let client: lc.LanguageClient


export function activate(context: vscode.ExtensionContext): void {

    // vscode.window.showInformationMessage('Crux-LLVM extension activated')

    const serverModule = context.asAbsolutePath(path.join('dist', 'server.bundle.js'))

    const debugOptions = {
        execArgv: [
            '--inspect=6005', // this must match the port in launch.json
            '--nolazy',
        ],
    }

    const serverOptions: lc.ServerOptions = {
        debug: {
            module: serverModule,
            transport: lc.TransportKind.ipc,
            options: debugOptions,
        },
        run: {
            module: serverModule,
            transport: lc.TransportKind.ipc,
        },
    }

    const clientOptions: lc.LanguageClientOptions = {
        documentSelector: [{ scheme: 'file', language: 'c' }],
        synchronize: {
            fileEvents: vscode.workspace.createFileSystemWatcher('**/*.c'),
        },
    }

    client = new lc.LanguageClient(
        'crux-llvm',
        'Crux-LLVM Language Server',
        serverOptions,
        clientOptions
    )

    context.subscriptions.push(

        vscode.window.registerWebviewViewProvider(
            CruxLLVMViewProvider.viewType,
            new CruxLLVMViewProvider(context, client),
        ),

    )

    client.start()

}


export function deactivate(): Promise<void> {
    if (!client) {
        return Promise.resolve()
    }
    return client.stop()
}
