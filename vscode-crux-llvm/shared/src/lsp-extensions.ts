import * as lsp from 'vscode-languageserver-protocol'

export const abortCruxLLVM = new lsp.NotificationType('crux-llvm/abort')
export const cruxLLVMAborted = new lsp.NotificationType('crux-llvm/aborted')
