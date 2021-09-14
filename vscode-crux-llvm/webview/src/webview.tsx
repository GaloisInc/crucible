import update from 'immutability-helper'
import * as React from 'react'
import * as ReactDOM from 'react-dom'
import { UnreachableCaseError } from 'ts-essentials'

import { CheckExecutableResult } from '@shared/check-executable-result'
import * as Configuration from '@shared/configuration'
import { webviewContainerId } from '@shared/constants'
import * as E2W from '@shared/extension-to-webview'
import * as W2E from '@shared/webview-to-extension'

import { handleCruxLLVMLog } from './crux-llvm-log-handler'
import { abortedIfNotDone, Goal, GoalStatus, showGoalStatus } from './goals'
import CSS from './styles/webview.css'


interface PersistedState {
    goals: Goal[]
    // results: string[]
}


interface VSCodeAPI {
    getState(): PersistedState | undefined
    setState(s: PersistedState): void
    postMessage(m: W2E.Message): void
}

declare const acquireVsCodeApi: () => VSCodeAPI
const vscode = acquireVsCodeApi()


const initialPersistedState: PersistedState = {
    goals: [],
}


function getPersistedState(): PersistedState {
    return vscode.getState() || initialPersistedState
}


interface WebviewWindow extends Window {
    [E2W.initialDataKey]: E2W.InitialData,
}
declare const window: WebviewWindow


const container = (document.getElementById(webviewContainerId) as unknown) as HTMLDivElement
if (container === null) {
    console.log(`Webview container with id ${webviewContainerId} is missing`)
} else {
    ReactDOM.render(
        <Webview
            initialData={window[E2W.initialDataKey]}
            vscode={vscode}
        />,
        container,
    )
}


type ReactSetter<T> = React.Dispatch<React.SetStateAction<T>>


function makeMessageListener(
    setters: {
        setConfiguration: ReactSetter<Configuration.Configuration>,
        setContent: ReactSetter<string>,
        setGoals: ReactSetter<Goal[]>,
        setStatusOfClang: ReactSetter<E2W.StatusOfClang>,
        setStatusOfCruxLLVM: ReactSetter<E2W.StatusOfCruxLLVM>,
        setStatusOfLLVMLink: ReactSetter<E2W.StatusOfLLVMLink>,
        setStatusOfZ3: ReactSetter<E2W.StatusOfZ3>,
        setValidationDiagnostics: ReactSetter<E2W.ValidationDiagnostics>,
        setValidationErrors: ReactSetter<E2W.ValidationError[]>,
        setValidationWarnings: ReactSetter<E2W.ValidationWarning[]>,
    },
) {
    return (message: E2W.Message) => {

        switch (message.tag) {

            case E2W.Tags.configurationChanged: {
                setters.setConfiguration(message.newConfiguration)
                break
            }

            case E2W.Tags.contentChanged: {
                setters.setContent(message.newContent)
                // if the content changed, we invalidate all diagnostics
                setters.setValidationDiagnostics(
                    E2W.makeValidationDiagnostics([]),
                )
                setters.setValidationErrors([])
                setters.setValidationWarnings([])
                break
            }

            case E2W.Tags.cruxLLVMAborted: {
                setters.setGoals(goals => {
                    return goals.map(goal => update(goal, { status: { $apply: abortedIfNotDone } }))
                })
                break
            }

            case E2W.Tags.cruxLLVMLogEntry: {
                handleCruxLLVMLog(setters, message)
                break
            }

            case E2W.Tags.statusOfClang: {
                setters.setStatusOfClang(message)
                break
            }

            case E2W.Tags.statusOfCruxLLVM: {
                setters.setStatusOfCruxLLVM(message)
                break
            }

            case E2W.Tags.statusOfLLVMLink: {
                setters.setStatusOfLLVMLink(message)
                break
            }

            case E2W.Tags.statusOfZ3: {
                setters.setStatusOfZ3(message)
                break
            }

            case E2W.Tags.validationDiagnostics: {
                setters.setValidationDiagnostics(message)
                break
            }

            case E2W.Tags.validationError: {
                setters.setValidationErrors(
                    (oldErrors) => update(oldErrors, { $push: [message] }),
                )
                break
            }

            case E2W.Tags.validationWarning: {
                setters.setValidationWarnings(
                    (oldWarnings) => update(oldWarnings, { $push: [message] }),
                )
                break
            }

            default: {
                // If you see a type error here, you're missing a case!
                throw new UnreachableCaseError(message)
            }

        }
    }
}


interface MessageEvent extends Event {
    readonly data: E2W.Message
}


export function Webview(props: {
    initialData: E2W.InitialData,
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

    /* On the first run, initialize the persisted state, if missing. */
    React.useEffect(
        () => {
            if (vscode.getState() === undefined) {
                vscode.setState(initialPersistedState)
            }
        },
        [],
    )

    const persistedState = getPersistedState()

    const [configuration, setConfiguration] = React.useState(initialConfiguration)

    // This one is only useful for debugging purposes
    const [, setContent] = React.useState(initialContent)

    const [goals, setGoals] = React.useState(persistedState.goals)

    const [statusOfClang, setStatusOfClang] = React.useState(initialStatusOfClang)
    const [statusOfCruxLLVM, setStatusOfCruxLLVM] = React.useState(initialStatusOfCruxLLVM)
    const [statusOfLLVMLink, setStatusOfLLVMLink] = React.useState(initialStatusOfLLVMLink)
    const [statusOfZ3, setStatusOfZ3] = React.useState(initialStatusOfZ3)

    const [, setValidationDiagnostics] = React.useState(initialValidationDiagnostics)
    const [, setValidationErrors] = React.useState(initialValidationErrors)
    const [, setValidationWarnings] = React.useState(initialValidationWarnings)

    // Persist state when it changes
    React.useEffect(
        () => {
            vscode.setState({
                goals,
            })
        },
        [goals],
    )

    React.useEffect(
        () => {
            const handler = (e: MessageEvent) => {
                return makeMessageListener(
                    {
                        setConfiguration,
                        setContent,
                        setGoals,
                        setStatusOfClang,
                        setStatusOfCruxLLVM,
                        setStatusOfLLVMLink,
                        setStatusOfZ3,
                        setValidationDiagnostics,
                        setValidationErrors,
                        setValidationWarnings,
                    },
                )(e.data)
            }
            window.addEventListener('message', handler)
            return () => {
                window.removeEventListener('message', handler)
            }
        },
        [],
    )

    // const diagnostics = validationDiagnostics.diagnostics.map((diagnostic, index) => (
    //     <tr key={index}>
    //         <td>{diagnostic.message}</td>
    //         <td>
    //             {diagnostic.range.start.line}:{diagnostic.range.start.character}
    //             -
    //             {diagnostic.range.end.line}:{diagnostic.range.end.character}
    //         </td>
    //     </tr>
    // ))

    // const errors = validationErrors.map(({ error }, index) => (
    //     <div key={index} className="error">{error}</div>
    // ))

    // const warnings = validationWarnings.map(({ warning }, index) => (
    //     <div key={index} className="warning">{warning}</div>
    // ))

    const goalsHeaderView = (
        <tr>
            <th className={CSS.goalNumber}>Goal number</th>
            {/* <th>Goal predicate</th> */}
            <th className={CSS.goalMessage}>Message</th>
            <th className={CSS.goalStatus}>Status</th>
        </tr>
    )

    const goalsView = goals.map(({ labeledPredMsg, status }, index) => (
        <tr key={index}>
            <td>{index}</td>
            {/* <td>{labeledPred}</td> */}
            <td>{labeledPredMsg.split('\n').slice(-1)[0]}</td>
            <td>{showGoalStatus(status)}</td>
        </tr>
    ))

    const abort = () => {
        vscode.postMessage({ tag: W2E.Tags.abortCruxLLVM } as W2E.Message)
    }

    return (
        <div>
            <details>
                <summary>Current configuration (click to unfold/refold)</summary>
                <table>
                    <tbody>
                        <tr>
                            <td>PATH (should contain z3)</td>
                            <td>{configuration[Configuration.ConfigurationKeys.PATH]}</td>
                            <td>{getIconForResult(statusOfZ3.status)}</td>
                            <td>{getTextForResult(statusOfZ3.status)}</td>
                        </tr>
                        <tr>
                            <td>clang</td>
                            <td>{configuration[Configuration.ConfigurationKeys.Clang]}</td>
                            <td>{getIconForResult(statusOfClang.status)}</td>
                            <td>{getTextForResult(statusOfClang.status)}</td>
                        </tr>
                        <tr>
                            <td>crux-llvm</td>
                            <td>{configuration[Configuration.ConfigurationKeys.CruxLLVM]}</td>
                            <td>{getIconForResult(statusOfCruxLLVM.status)}</td>
                            <td>{getTextForResult(statusOfCruxLLVM.status)}</td>
                        </tr>
                        <tr>
                            <td>llvm-link</td>
                            <td>{configuration[Configuration.ConfigurationKeys.LLVMLink]}</td>
                            <td>{getIconForResult(statusOfLLVMLink.status)}</td>
                            <td>{getTextForResult(statusOfLLVMLink.status)}</td>
                        </tr>
                    </tbody>
                </table>
                <div>--include-dirs: {configuration[Configuration.ConfigurationKeys.IncludeDirs]}</div>
            </details>
            {/* <div>Diagnostics:
                <table><tbody>{diagnostics}</tbody></table>
            </div> */}
            {/* <div>{errors}</div>
            <div>{warnings}</div> */}
            <button onClick={abort}>Abort</button>
            <table>
                <thead>
                    {goalsHeaderView}
                </thead>
                <tbody>
                    {goalsView}
                </tbody>
            </table>
            {/* <div>Content being checked: {content}</div> */}
        </div >
    )

}


function getIconForResult(
    result: CheckExecutableResult,
): JSX.Element {
    if (result.check) {
        return <i className="codicon codicon-check ok" />
    } else {
        return <i className="codicon codicon-chrome-close error" />
    }
}


function getTextForResult(
    result: CheckExecutableResult,
): string {
    if (result.check) {
        return result.output.toString() // should not be needed but debugging
    } else {
        return result.errorMessage.toString() // should not be needed but debugging
    }
}
