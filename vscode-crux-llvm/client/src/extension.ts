import * as path from 'path'

import * as vscode from 'vscode'
import {
    LanguageClient,
    LanguageClientOptions,
    TransportKind,
} from 'vscode-languageclient/node'

export const webviewContainerId = 'webview-container'

let client: LanguageClient

class CruxLLVMViewProvider implements vscode.WebviewViewProvider {

    public static readonly viewType = 'vscode-crux-llvm-panel-view'
    readonly #context: vscode.ExtensionContext

    constructor(
        context: vscode.ExtensionContext,
    ) {
        this.#context = context
    }

    public resolveWebviewView(
        webviewView: vscode.WebviewView,
        _context: vscode.WebviewViewResolveContext,
        _token: vscode.CancellationToken,
    ) {
        // const dist = this.#context.asAbsolutePath('dist')

        webviewView.webview.options = {
            enableScripts: true,
            localResourceRoots: [
                this.#context.extensionUri,
                vscode.Uri.joinPath(this.#context.extensionUri, 'dist', 'webview.bundle.js'),
            ],
        }

        webviewView.webview.html = this.getHTMLForWebview(webviewView.webview)
    }

    getHTMLForWebview(webview: vscode.Webview): string {
        const extensionUri = this.#context.extensionUri

        const scriptUri = webview.asWebviewUri(
            vscode.Uri.joinPath(extensionUri, 'dist', 'webview.bundle.js')
        )

        // const styleResetUri = webview.asWebviewUri(vscode.Uri.joinPath(extensionUri, 'media', 'reset.css'))
        // const styleVSCodeUri = webview.asWebviewUri(vscode.Uri.joinPath(extensionUri, 'media', 'vscode.css'))
        // const styleMainUri = webview.asWebviewUri(vscode.Uri.joinPath(extensionUri, 'media', 'main.css'))

        // this allows the content security policy to allow execution of exactly
        // the one script with this random identifier
        const nonce = getNonce()

        return `
            <!DOCTYPE html>
			<html lang="en">
			<head>
                <meta charset="UTF-8">
                <meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src ${webview.cspSource}; script-src 'nonce-${nonce}';">
                <meta name="viewport" content="width=device-width, initial-scale=1.0">
                <title>Cat Colors</title>
			</head>
			<body>
                <div id="${webviewContainerId}" />
                <script nonce="${nonce}" src="${scriptUri}"></script>
			</body>
			</html>
        `
    }
}

export function activate(context: vscode.ExtensionContext): void {

    const cruxLLVMViewProvider = new CruxLLVMViewProvider(context)

    context.subscriptions.push(
        vscode.window.registerWebviewViewProvider(
            CruxLLVMViewProvider.viewType,
            cruxLLVMViewProvider,
        ),
    )

    vscode.window.showInformationMessage('Crux-LLVM extension activated')

    const serverModule = context.asAbsolutePath(path.join('dist', 'server.bundle.js'))

    const debugOptions = {
        execArgv: [
            '--inspect=6009',
            '--nolazy',
        ],
    }

    const serverOptions = {
        run: {
            module: serverModule,
            transport: TransportKind.ipc,
        },
        debug: {
            module: serverModule,
            transport: TransportKind.ipc,
            options: debugOptions,
        },
    }

    const clientOptions: LanguageClientOptions = {
        documentSelector: [{ scheme: 'file', language: 'c' }],
        synchronize: {
            fileEvents: vscode.workspace.createFileSystemWatcher('**/*.c'),
        },
    }

    client = new LanguageClient(
        'crux-llvm',
        'Crux-LLVM Language Server',
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

function getNonce() {
    let text = ''
    const possible = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789'
    for (let i = 0; i < 32; i++) {
        text += possible.charAt(Math.floor(Math.random() * possible.length))
    }
    return text
}
