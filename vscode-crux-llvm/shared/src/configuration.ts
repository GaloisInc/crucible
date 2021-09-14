// Make sure to keep this updated with the declarations in package.json
export enum ConfigurationKeys {
    Clang = 'clang',
    CruxLLVM = 'crux-llvm',
    Debug = 'debug',
    IncludeDirs = 'include-dirs',
    LLVMLink = 'llvm-link',
    PATH = 'path',
}


// Sometimes, we want to consider all executables
export type KeyOfExecutable
    = ConfigurationKeys.CruxLLVM
    | ConfigurationKeys.Clang
    | ConfigurationKeys.LLVMLink


// Type used by the webview to retain information about the current
// configuration
export type Configuration = {
    [ConfigurationKeys.CruxLLVM]: string
    [ConfigurationKeys.Clang]: string
    [ConfigurationKeys.Debug]: string
    [ConfigurationKeys.IncludeDirs]: string[]
    [ConfigurationKeys.LLVMLink]: string
    [ConfigurationKeys.PATH]: string
}
