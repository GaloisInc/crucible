import * as vscode from 'vscode'
import * as lc from 'vscode-languageclient/node'

import { checkExecutable, checkExecutableViaPATH } from '@shared/check-executable'
import { ConfigurationKeys } from '@shared/configuration'
import * as Constants from '@shared/constants'
import * as E2W from '@shared/extension-to-webview'
import * as LSPExtensions from '@shared/lsp-extensions'

import * as Configuration from './configuration'
import { onDidChangeConfiguration } from './configuration-watcher'
import { createWebsocketServer } from './websocket-server'
import * as WebviewMessageHandler from './webview-message-handler'


export class CruxLLVMViewProvider implements vscode.WebviewViewProvider {

    public static readonly viewType = 'vscode-crux-llvm-panel-view'

    constructor(
        private context: vscode.ExtensionContext,
        private client: lc.LanguageClient,
    ) {
    }

    public resolveWebviewView(
        webviewView: vscode.WebviewView,
        _context: vscode.WebviewViewResolveContext,
        _token: vscode.CancellationToken,
    ): void {

        const stylesheetURI = vscode.Uri.joinPath(this.context.extensionUri, 'dist', 'static', 'style.css')
        const webviewBundleURI = vscode.Uri.joinPath(this.context.extensionUri, 'dist', 'webview.bundle.js')

        const vscodeCodiconURI = (
            vscode.Uri.joinPath(this.context.extensionUri, 'dist', 'vscode-codicons')
        )
        const vscodeCodiconsCSS = vscode.Uri.joinPath(vscodeCodiconURI, 'codicon.css')
        const vscodeCodiconsTTF = vscode.Uri.joinPath(vscodeCodiconURI, 'codicon.ttf')

        const webview = webviewView.webview

        webview.options = {
            enableScripts: true,
            localResourceRoots: [
                this.context.extensionUri,
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
                        tag: E2W.Tags.cruxLLVMLogEntry,
                        logEntry: JSON.parse(msg.utf8Data),
                    } as E2W.Message)
                }
            }
        )

        this.context.subscriptions.push(

            vscode.workspace.onDidChangeConfiguration(onDidChangeConfiguration(webviewView)),

            vscode.workspace.onDidChangeTextDocument((e) => {
                webview.postMessage({
                    tag: E2W.Tags.contentChanged,
                    newContent: e.document.getText(),
                } as E2W.Message)
            }),

            webview.onDidReceiveMessage(
                WebviewMessageHandler.makeHandler(this.client)
            ),

            // When the LSP server aborts Crux-LLVM, we let the webview know.
            this.client.onNotification(LSPExtensions.cruxLLVMAborted, () => {
                webview.postMessage({
                    tag: E2W.Tags.cruxLLVMAborted,
                } as E2W.Message)
            }),

        )


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

        const configuration = Configuration.fromWorkspaceConfiguration(Configuration.getConfiguration())
        const initialStatusOfClang = checkExecutable(configuration, ConfigurationKeys.Clang)
        const initialStatusOfCruxLLVM = checkExecutable(configuration, ConfigurationKeys.CruxLLVM)
        const initialStatusOfLLVMLink = checkExecutable(configuration, ConfigurationKeys.LLVMLink)
        const initialStatusOfZ3 = checkExecutableViaPATH(configuration, 'z3')

        const content = vscode.window.activeTextEditor?.document.getText()

        const initialData: E2W.InitialData = {

            initialConfiguration: Configuration.fromWorkspaceConfiguration(Configuration.getConfiguration()),

            initialContent: content || '',

            initialStatusOfClang:
                E2W.makeStatusOfClang(initialStatusOfClang),
            initialStatusOfCruxLLVM:
                E2W.makeStatusOfCruxLLVM(initialStatusOfCruxLLVM),
            initialStatusOfLLVMLink:
                E2W.makeStatusOfLLVMLink(initialStatusOfLLVMLink),
            initialStatusOfZ3:
                E2W.makeStatusOfZ3(initialStatusOfZ3),

            // there is no reasonable way of initializing these as they could
            // take a long time to compute
            initialValidationDiagnostics: E2W.makeValidationDiagnostics([]),
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
                    window.${E2W.initialDataKey} = ${JSON.stringify(initialData)}
                </script>
                <div id="${Constants.webviewContainerId}" />
                <script nonce="${nonce}" src="${uris.webviewBundle}" />
			</body>
			</html>
        `
    }
}


function getNonce() {
    let text = ''
    const possible = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789'
    for (let i = 0; i < 32; i++) {
        text += possible.charAt(Math.floor(Math.random() * possible.length))
    }
    return text
}
