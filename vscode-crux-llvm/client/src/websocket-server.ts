import * as http from 'http'

import * as bytes from 'bytes'
import * as ws from 'websocket'

import * as Constants from '@shared/constants'

/**
* To listen for the results from crux-llvm, we need a websocket listening on
* a port.  The port will be communicated to the crux-llvm-for-ide process
* when spawned.
*
* This server could be held by the client or the server, it does not matter
* much.  Since the output will be sent to the webview, it seems currently
* easier to have the server in the client (one fewer hoops to jump).
*
* @param onMessage - Callback for handling messages
*/
export function createWebsocketServer(
    onMessage: (msg: ws.Message) => void,
): void {

    const httpServer = http.createServer((req, rsp) => {
        console.log(req, rsp)
        rsp.end()
    })

    httpServer.listen(Constants.websocketPort, () => {
        console.log('HTTP server listening')
    })

    const server = new ws.server({
        httpServer,
        maxReceivedFrameSize: bytes('10 MB'),
        maxReceivedMessageSize: bytes('10 MB'),
    })

    server.on('request', req => {
        const wsConnection = req.accept()
        wsConnection.on('message', onMessage)
    })

    server.on('close', c => {
        /**
         * NOTE: if you ever get a reason code of 1009, it means the server sent
         * a message too large.  You can accept larger messages by tweaking
         * 'maxReceivedMessageSize'.
         */
        console.log(`Server closing: ${c.closeReasonCode}`)
    })

}
