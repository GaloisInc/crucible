import { Diagnostic } from 'vscode-languageserver'

import { CheckCommandResult } from './check-command-result'
import { Configuration } from './configuration'

export const initialDataKey = 'initialData'
export interface InitialData {
    readonly initialConfiguration: Configuration
    readonly initialContent: string
    readonly initialStatusOfClang: StatusOfClang
    readonly initialStatusOfCruxLLVM: StatusOfCruxLLVM
    readonly initialStatusOfLLVMLink: StatusOfLLVMLink
    readonly initialStatusOfZ3: StatusOfZ3
    readonly initialValidationDiagnostics: ValidationDiagnostics
    readonly initialValidationErrors: ValidationError[]
    readonly initialValidationWarnings: ValidationWarning[]
}

export type ExtensionToWebview = (
    ConfigurationChanged
    | ContentChanged
    | CruxLLVMLogEntry
    | StatusOfClang
    | StatusOfCruxLLVM
    | StatusOfLLVMLink
    | StatusOfZ3
    | ValidationDiagnostics
    | ValidationError
    | ValidationWarning
)

export const configurationChanged = 'ConfigurationChanged'
export interface ConfigurationChanged {
    readonly tag: typeof configurationChanged
    readonly newConfiguration: Configuration
}

export const contentChanged = 'ContentChanged'
export interface ContentChanged {
    readonly tag: typeof contentChanged
    readonly newContent: string
}

export const cruxLLVMLogEntry = 'CruxLLVMLogEntry'
export interface CruxLLVMLogEntry {
    readonly tag: typeof cruxLLVMLogEntry
    readonly logEntry: CruxLLVMLogging
}

export const statusOfClang = 'StatusOfClang'
export interface StatusOfClang {
    readonly tag: typeof statusOfClang
    readonly status: CheckCommandResult
}
export function makeStatusOfClang(status: CheckCommandResult): StatusOfClang {
    return { tag: statusOfClang, status }
}

export const statusOfCruxLLVM = 'StatusOfCruxLLVM'
export interface StatusOfCruxLLVM {
    readonly tag: typeof statusOfCruxLLVM
    readonly status: CheckCommandResult
}
export function makeStatusOfCruxLLVM(status: CheckCommandResult): StatusOfCruxLLVM {
    return { tag: statusOfCruxLLVM, status }
}

export const statusOfLLVMLink = 'StatusOfLLVMLink'
export interface StatusOfLLVMLink {
    readonly tag: typeof statusOfLLVMLink
    readonly status: CheckCommandResult
}
export function makeStatusOfLLVMLink(status: CheckCommandResult): StatusOfLLVMLink {
    return { tag: statusOfLLVMLink, status }
}

export const statusOfZ3 = 'StatusOfZ3'
export interface StatusOfZ3 {
    readonly tag: typeof statusOfZ3
    readonly status: CheckCommandResult
}
export function makeStatusOfZ3(status: CheckCommandResult): StatusOfZ3 {
    return { tag: statusOfZ3, status }
}

export const validationDiagnostics = 'ValidationDiagnostics'
export interface ValidationDiagnostics {
    readonly tag: typeof validationDiagnostics
    readonly diagnostics: Diagnostic[]
}
export function makeValidationDiagnostics(diagnostics: Diagnostic[]): ValidationDiagnostics {
    return { tag: validationDiagnostics, diagnostics }
}

export const validationError = 'ValidationError'
export interface ValidationError {
    readonly tag: typeof validationError
    readonly error: string
}
export function makeValidationError(error: string): ValidationError {
    return { tag: validationError, error }
}

export const validationWarning = 'ValidationWarning'
export interface ValidationWarning {
    readonly tag: typeof validationWarning
    readonly warning: string
}
export function makeValidationWarning(warning: string): ValidationWarning {
    return { tag: validationWarning, warning }
}
