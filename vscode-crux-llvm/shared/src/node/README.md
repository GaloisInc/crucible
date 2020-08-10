This directory is for shared content between the language server and the
language client that depends on Node, typically because it does file system
access.

As a consequence, it can **not** be imported in the webview, since the webview
is transpiled to pure ES6 and does not run in a Node environment.  If you need
to run code from this directory for something in the webview, you should use the
communication channels to have the webview request the code be run by the
extension client, and have the extension client send the result via
'postMessage'.
