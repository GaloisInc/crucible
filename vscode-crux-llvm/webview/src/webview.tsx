import update from 'immutability-helper'
import * as React from 'react'
import * as ReactDOM from 'react-dom'

import { CheckCommandResult } from '@shared/check-command-result'
import * as Configuration from '@shared/configuration'
import { webviewContainerId } from '@shared/constants'
import * as ExtensionToWebview from '@shared/extension-to-webview'


interface PersistedState {
    results: string[]
}

interface VSCodeAPI {
    getState(): PersistedState | undefined
    setState(s: PersistedState): void
}

declare const acquireVsCodeApi: () => VSCodeAPI
const vscode = acquireVsCodeApi()

interface WebviewWindow extends Window {
    [ExtensionToWebview.initialDataKey]: ExtensionToWebview.InitialData,
}
declare const window: WebviewWindow

const container = (document.getElementById(webviewContainerId) as unknown) as HTMLDivElement
if (container === null) {
    console.log(`Webview container with id ${webviewContainerId} is missing`)
} else {
    ReactDOM.render(
        <Webview
            initialData={window[ExtensionToWebview.initialDataKey]}
            vscode={vscode}
        />,
        container,
    )
}

type ReactSetter<T> = React.Dispatch<React.SetStateAction<T>>

function makeMessageListener(setters: {
    setConfiguration: ReactSetter<Configuration.Configuration>,
    setContent: ReactSetter<string>,
    setStatusOfClang: ReactSetter<ExtensionToWebview.StatusOfClang>,
    setStatusOfCruxLLVM: ReactSetter<ExtensionToWebview.StatusOfCruxLLVM>,
    setStatusOfLLVMLink: ReactSetter<ExtensionToWebview.StatusOfLLVMLink>,
    setStatusOfZ3: ReactSetter<ExtensionToWebview.StatusOfZ3>,
    setValidationDiagnostics: ReactSetter<ExtensionToWebview.ValidationDiagnostics>,
    setValidationErrors: ReactSetter<ExtensionToWebview.ValidationError[]>,
    setValidationWarnings: ReactSetter<ExtensionToWebview.ValidationWarning[]>,
}) {
    return (message: ExtensionToWebview.ExtensionToWebview) => {
        switch (message.tag) {

            case ExtensionToWebview.configurationChanged: {
                setters.setConfiguration(message.newConfiguration)
                break
            }

            case ExtensionToWebview.contentChanged: {
                setters.setContent(message.newContent)
                // if the content changed, we invalidate all diagnostics
                setters.setValidationDiagnostics(
                    ExtensionToWebview.makeValidationDiagnostics([]),
                )
                setters.setValidationErrors([])
                setters.setValidationWarnings([])
                break
            }

            case ExtensionToWebview.statusOfClang: {
                setters.setStatusOfClang(message)
                break
            }

            case ExtensionToWebview.statusOfCruxLLVM: {
                setters.setStatusOfCruxLLVM(message)
                break
            }

            case ExtensionToWebview.statusOfLLVMLink: {
                setters.setStatusOfLLVMLink(message)
                break
            }

            case ExtensionToWebview.statusOfZ3: {
                setters.setStatusOfZ3(message)
                break
            }

            case ExtensionToWebview.validationDiagnostics: {
                setters.setValidationDiagnostics(message)
                break
            }

            case ExtensionToWebview.validationError: {
                setters.setValidationErrors(
                    (oldErrors) => update(oldErrors, { $push: [message] }),
                )
                break
            }

            case ExtensionToWebview.validationWarning: {
                setters.setValidationWarnings(
                    (oldWarnings) => update(oldWarnings, { $push: [message] }),
                )
                break
            }

        }
    }
}

interface MessageEvent extends Event {
    readonly data: ExtensionToWebview.ExtensionToWebview
}

export function Webview(props: {
    initialData: ExtensionToWebview.InitialData,
    vscode: VSCodeAPI,
}): JSX.Element {

    const {
        initialConfiguration,
        initialContent,
        initialStatusOfClang,
        initialStatusOfCruxLLVM,
        initialStatusOfLLVMLink,
        initialStatusOfZ3,
        initialValidationDiagnostics,
        initialValidationErrors,
        initialValidationWarnings,
    } = props.initialData

    const [configuration, setConfiguration] = React.useState(initialConfiguration)
    const [content, setContent] = React.useState(initialContent)

    const [statusOfClang, setStatusOfClang] = React.useState(initialStatusOfClang)
    const [statusOfCruxLLVM, setStatusOfCruxLLVM] = React.useState(initialStatusOfCruxLLVM)
    const [statusOfLLVMLink, setStatusOfLLVMLink] = React.useState(initialStatusOfLLVMLink)
    const [statusOfZ3, setStatusOfZ3] = React.useState(initialStatusOfZ3)

    const [validationDiagnostics, setValidationDiagnostics] = React.useState(initialValidationDiagnostics)
    const [validationErrors, setValidationErrors] = React.useState(initialValidationErrors)
    const [validationWarnings, setValidationWarnings] = React.useState(initialValidationWarnings)

    React.useEffect(() => {
        const handler = (e: MessageEvent) => {
            return makeMessageListener({
                setConfiguration,
                setContent,
                setStatusOfClang,
                setStatusOfCruxLLVM,
                setStatusOfLLVMLink,
                setStatusOfZ3,
                setValidationDiagnostics,
                setValidationErrors,
                setValidationWarnings,
            })(e.data)
        }
        window.addEventListener('message', handler)
        return () => {
            window.removeEventListener('message', handler)
        }
    })

    const diagnostics = validationDiagnostics.diagnostics.map((diagnostic, index) => (
        <tr key={index}>
            <td>{diagnostic.message}</td>
            <td>
                {diagnostic.range.start.line}:{diagnostic.range.start.character}
                -
                {diagnostic.range.end.line}:{diagnostic.range.end.character}
            </td>
        </tr>
    ))

    const errors = validationErrors.map(({ error }, index) => (
        <div key={index} className="error">{error}</div>
    ))

    const warnings = validationWarnings.map(({ warning }, index) => (
        <div key={index} className="warning">{warning}</div>
    ))

    return (
        <div>
            <details>
                <summary>Current configuration</summary>
                <table>
                    <tbody>
                        <tr>
                            <td>PATH (should contain z3)</td>
                            <td>{configuration[Configuration.configPATH]}</td>
                            <td>{getIconForResult(statusOfZ3.status)}</td>
                            <td>{getTextForResult(statusOfZ3.status)}</td>
                        </tr>
                        <tr>
                            <td>clang</td>
                            <td>{configuration[Configuration.configClang]}</td>
                            <td>{getIconForResult(statusOfClang.status)}</td>
                            <td>{getTextForResult(statusOfClang.status)}</td>
                        </tr>
                        <tr>
                            <td>crux-llvm</td>
                            <td>{configuration[Configuration.configCruxLLVM]}</td>
                            <td>{getIconForResult(statusOfCruxLLVM.status)}</td>
                            <td>{getTextForResult(statusOfCruxLLVM.status)}</td>
                        </tr>
                        <tr>
                            <td>llvm-link</td>
                            <td>{configuration[Configuration.configLLVMLink]}</td>
                            <td>{getIconForResult(statusOfLLVMLink.status)}</td>
                            <td>{getTextForResult(statusOfLLVMLink.status)}</td>
                        </tr>
                    </tbody>
                </table>
                <div>--include-dirs: {configuration[Configuration.configIncludeDirs]}</div>
            </details>
            <div>Diagnostics:
                <table><tbody>{diagnostics}</tbody></table>
            </div>
            <div>{errors}</div>
            <div>{warnings}</div>
            <div>Content being checked: {content}</div>
        </div >
    )

}

function getIconForResult(
    result: CheckCommandResult,
): JSX.Element {
    if (result.check) {
        return <i className="codicon codicon-check ok" />
    } else {
        return <i className="codicon codicon-chrome-close error" />
    }
}

function getTextForResult(
    result: CheckCommandResult,
): string {
    if (result.check) {
        return result.output.toString() // should not be needed but debugging
    } else {
        return result.errorMessage.toString() // should not be needed but debugging
    }
}
