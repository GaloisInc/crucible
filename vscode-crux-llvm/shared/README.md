This directory is for content that needs to be shared between the extension
client, and the webview.  Because the former needs to be compiled as a CommonJS
module, but the latter needs to be compiled as ES6, neither is able to import
the other.  Therefore, they need a common place to share code and definitions
that they may each refer to and compile as they see fit.
