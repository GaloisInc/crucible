import * as React from 'react'
import * as ReactDOM from 'react-dom'

const webviewContainerId = 'webview-container'
// import { webviewContainerId } from '@client/extension'

// declare const acquireVsCodeApi: () => void
// const vscode = acquireVsCodeApi()

const container = (document.getElementById(webviewContainerId) as unknown) as HTMLDivElement
if (container === null) {
    console.log(`Webview container with id ${webviewContainerId} is missing`)
} else {
    ReactDOM.render(
        <Webview />,
        container,
    )
}

export function Webview(): JSX.Element {
    return <div>Webview is loaded!</div>
}
