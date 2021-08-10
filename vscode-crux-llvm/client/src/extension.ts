import * as path from 'path'

import * as vscode from 'vscode'
import * as LanguageClientNode from 'vscode-languageclient/node'

import * as Configuration from '@shared/configuration'
import * as Constants from '@shared/constants'
import * as ExtensionToWebview from '@shared/extension-to-webview'
import { checkCommand, checkCommandViaPATH } from '@shared/node/check-command'

import { createWebsocketServer } from './websocket-server'


let client: LanguageClientNode.LanguageClient

function getConfiguration(): Configuration.Configuration {
    const result = vscode.workspace.getConfiguration(Constants.settingsName)
    return (result as unknown as Configuration.Configuration)
}

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

        const stylesheetURI = vscode.Uri.joinPath(this.#context.extensionUri, 'dist', 'static', 'style.css')
        const webviewBundleURI = vscode.Uri.joinPath(this.#context.extensionUri, 'dist', 'webview.bundle.js')

        const vscodeCodiconURI = (
            vscode.Uri.joinPath(this.#context.extensionUri, 'dist', 'vscode-codicons')
        )
        const vscodeCodiconsCSS = vscode.Uri.joinPath(vscodeCodiconURI, 'codicon.css')
        const vscodeCodiconsTTF = vscode.Uri.joinPath(vscodeCodiconURI, 'codicon.ttf')

        const webview = webviewView.webview

        webview.options = {
            enableScripts: true,
            localResourceRoots: [
                this.#context.extensionUri,
                vscodeCodiconsCSS,
                vscodeCodiconsTTF,
                webviewBundleURI,
            ],
        }

        // FIXME: wrap this in a Disposable so we can let VSCode close the server
        createWebsocketServer(
            msg => {
                if (msg.type === 'utf8') {
                    // console.log(msg.utf8Data)
                    webview.postMessage({
                        tag: ExtensionToWebview.cruxLLVMLogEntry,
                        logEntry: JSON.parse(msg.utf8Data),
                    } as ExtensionToWebview.CruxLLVMLogEntry)
                }
            }
        )

        vscode.workspace.onDidChangeConfiguration((e) => {

            if (e.affectsConfiguration(Constants.settingsName)) {
                webviewView.webview.postMessage({
                    tag: ExtensionToWebview.configurationChanged,
                    newConfiguration: getConfiguration(),
                } as ExtensionToWebview.ConfigurationChanged)
            }

            const postMessageIfAffected =
                <
                    Key extends keyof Configuration.Configuration,
                    SubConfiguration extends Configuration.Configuration & Record<Key, string>
                >(
                    field: Key,
                    messageTag: string,
                ) => {
                    if (e.affectsConfiguration(`${Constants.settingsName}.${field}`)) {
                        const newStatus = checkCommand<Key, SubConfiguration>(getConfiguration(), field)
                        webviewView.webview.postMessage({
                            tag: messageTag,
                            status: newStatus,
                        })
                    }
                }

            postMessageIfAffected(
                Configuration.configClang,
                ExtensionToWebview.statusOfClang,
            )
            postMessageIfAffected(
                Configuration.configCruxLLVM,
                ExtensionToWebview.statusOfCruxLLVM,
            )
            postMessageIfAffected(
                Configuration.configLLVMLink,
                ExtensionToWebview.statusOfLLVMLink,
            )

        })

        vscode.workspace.onDidChangeTextDocument((e) => {

            webview.postMessage({
                tag: ExtensionToWebview.contentChanged,
                newContent: e.document.getText(),
            } as ExtensionToWebview.ContentChanged)

            // validateTextDocument(
            //     getConfiguration(),
            //     e.document.uri.fsPath,
            //     {

            //         onDiagnostics: (diagnostics) => {
            //             webview.postMessage({
            //                 tag: ExtensionToWebview.validationDiagnostics,
            //                 diagnostics,
            //             } as ExtensionToWebview.ValidationDiagnostics)
            //         },

            //         onError: (error) => {
            //             webview.postMessage({
            //                 tag: ExtensionToWebview.validationError,
            //                 error,
            //             } as ExtensionToWebview.ValidationError)
            //         },

            //         onWarning: (warning) => {
            //             webview.postMessage({
            //                 tag: ExtensionToWebview.validationWarning,
            //                 warning,
            //             } as ExtensionToWebview.ValidationWarning)
            //         },

            //     },
            // )

        })

        // All URIs must be transformed from local filesystem URIs to webview
        // URIs.
        webview.html = this.getHTMLForWebview(
            webview.cspSource,
            {
                stylesheet: webview.asWebviewUri(stylesheetURI),
                vscodeCodiconsCSS: webview.asWebviewUri(vscodeCodiconsCSS),
                vscodeCodiconsTTF: webview.asWebviewUri(vscodeCodiconsTTF),
                webviewBundle: webview.asWebviewUri(webviewBundleURI),
            },
        )

    }

    getHTMLForWebview(
        cspSource: string,
        uris: {
            stylesheet: vscode.Uri,
            vscodeCodiconsCSS: vscode.Uri,
            vscodeCodiconsTTF: vscode.Uri,
            webviewBundle: vscode.Uri,
        },
    ): string {

        // this allows the content security policy to allow execution of exactly
        // the scripts with this random identifier
        const nonce = getNonce()

        const configuration = getConfiguration()
        const initialStatusOfClang = checkCommand(configuration, Configuration.configClang)
        const initialStatusOfCruxLLVM = checkCommand(configuration, Configuration.configCruxLLVM)
        const initialStatusOfLLVMLink = checkCommand(configuration, Configuration.configLLVMLink)
        const initialStatusOfZ3 = checkCommandViaPATH(configuration, 'z3')

        const content = vscode.window.activeTextEditor?.document.getText()

        const initialData: ExtensionToWebview.InitialData = {

            initialConfiguration: getConfiguration(),
            initialContent: content || '',

            initialStatusOfClang:
                ExtensionToWebview.makeStatusOfClang(initialStatusOfClang),
            initialStatusOfCruxLLVM:
                ExtensionToWebview.makeStatusOfCruxLLVM(initialStatusOfCruxLLVM),
            initialStatusOfLLVMLink:
                ExtensionToWebview.makeStatusOfLLVMLink(initialStatusOfLLVMLink),
            initialStatusOfZ3:
                ExtensionToWebview.makeStatusOfZ3(initialStatusOfZ3),

            // there is no reasonable way of initializing these as they could
            // take a long time to compute
            initialValidationDiagnostics: ExtensionToWebview.makeValidationDiagnostics([]),
            initialValidationErrors: [],
            initialValidationWarnings: [],

        }

        return `
            <!DOCTYPE html>
                <html lang="en">
                <head>
                <meta charset="UTF-8">
				<meta http-equiv="Content-Security-Policy" content="
                    default-src 'none';
                    font-src ${uris.vscodeCodiconsTTF.path};
                    style-src ${cspSource} ${uris.vscodeCodiconsCSS.path};
                    script-src 'nonce-${nonce}';
                ">
				<meta name="viewport" content="width=device-width, initial-scale=1.0">
				<title>VSCode Crux-LLVM</title>
				<link href="${uris.stylesheet}" rel="stylesheet" />
				<link href="${uris.vscodeCodiconsCSS}" rel="stylesheet" />
			</head>
			<body>
                <script nonce="${nonce}" type="text/javascript">
                    window.${ExtensionToWebview.initialDataKey} = ${JSON.stringify(initialData)}
                </script>
                <div id="${Constants.webviewContainerId}" />
                <script nonce="${nonce}" src="${uris.webviewBundle}" />
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

    // vscode.window.showInformationMessage('Crux-LLVM extension activated')

    const serverModule = context.asAbsolutePath(path.join('dist', 'server.bundle.js'))

    const debugOptions = {
        execArgv: [
            '--inspect=6005', // this must match the port in launch.json
            '--nolazy',
        ],
    }

    const serverOptions: LanguageClientNode.ServerOptions = {
        debug: {
            module: serverModule,
            transport: LanguageClientNode.TransportKind.ipc,
            options: debugOptions,
        },
        run: {
            module: serverModule,
            transport: LanguageClientNode.TransportKind.ipc,
        },
    }

    const clientOptions: LanguageClientNode.LanguageClientOptions = {
        documentSelector: [{ scheme: 'file', language: 'c' }],
        synchronize: {
            fileEvents: vscode.workspace.createFileSystemWatcher('**/*.c'),
        },
    }

    client = new LanguageClientNode.LanguageClient(
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
