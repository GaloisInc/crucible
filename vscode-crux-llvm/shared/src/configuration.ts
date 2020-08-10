// Make sure to keep this updated with the declarations in package.json

export const configCruxLLVM = 'crux-llvm'
export const configClang = 'clang'
export const configDebug = 'debug'
export const configIncludeDirs = 'include-dirs'
export const configLLVMLink = 'llvm-link'
export const configPATH = 'path'

export type Configuration = {
    [configCruxLLVM]: string
    [configClang]: string
    [configDebug]: string
    [configIncludeDirs]: string
    [configLLVMLink]: string
    [configPATH]: string
}
