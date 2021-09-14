import { Diagnostic } from 'vscode-languageserver'

import { CheckExecutableResult } from './check-executable-result'
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


export enum Tags {
    configurationChanged = 'ConfigurationChanged',
    contentChanged = 'ContentChanged',
    cruxLLVMAborted = 'CruxLLVMAborted',
    cruxLLVMLogEntry = 'CruxLLVMLogEntry',
    statusOfClang = 'StatusOfClang',
    statusOfCruxLLVM = 'StatusOfCruxLLVM',
    statusOfLLVMLink = 'StatusOfLLVMLink',
    statusOfZ3 = 'StatusOfZ3',
    validationDiagnostics = 'ValidationDiagnostics',
    validationError = 'ValidationError',
    validationWarning = 'ValidationWarning',
}


export type Message
    = ConfigurationChanged
    | ContentChanged
    | CruxLLVMAborted
    | CruxLLVMLogEntry
    | StatusOfClang
    | StatusOfCruxLLVM
    | StatusOfLLVMLink
    | StatusOfZ3
    | ValidationDiagnostics
    | ValidationError
    | ValidationWarning


export type ConfigurationChanged = {
    readonly tag: Tags.configurationChanged
    readonly newConfiguration: Configuration
}

export type ContentChanged = {
    readonly tag: Tags.contentChanged
    readonly newContent: string
}

export type CruxLLVMAborted = {
    readonly tag: Tags.cruxLLVMAborted
}

export type CruxLLVMLogEntry = {
    readonly tag: Tags.cruxLLVMLogEntry
    readonly logEntry: CruxLLVMLogging
}


export type StatusOfClang = {
    readonly tag: Tags.statusOfClang
    readonly status: CheckExecutableResult
}

export function makeStatusOfClang(status: CheckExecutableResult): StatusOfClang {
    return { tag: Tags.statusOfClang, status }
}


export type StatusOfCruxLLVM = {
    readonly tag: Tags.statusOfCruxLLVM
    readonly status: CheckExecutableResult
}

export function makeStatusOfCruxLLVM(status: CheckExecutableResult): StatusOfCruxLLVM {
    return { tag: Tags.statusOfCruxLLVM, status }
}


export type StatusOfLLVMLink = {
    readonly tag: Tags.statusOfLLVMLink
    readonly status: CheckExecutableResult
}

export function makeStatusOfLLVMLink(status: CheckExecutableResult): StatusOfLLVMLink {
    return { tag: Tags.statusOfLLVMLink, status }
}


export type StatusOfZ3 = {
    readonly tag: Tags.statusOfZ3
    readonly status: CheckExecutableResult
}

export function makeStatusOfZ3(status: CheckExecutableResult): StatusOfZ3 {
    return { tag: Tags.statusOfZ3, status }
}

export type ValidationDiagnostics = {
    readonly tag: Tags.validationDiagnostics
    readonly diagnostics: Diagnostic[]
}

export function makeValidationDiagnostics(diagnostics: Diagnostic[]): ValidationDiagnostics {
    return { tag: Tags.validationDiagnostics, diagnostics }
}


export type ValidationError = {
    readonly tag: Tags.validationError
    readonly error: string
}

export function makeValidationError(error: string): ValidationError {
    return { tag: Tags.validationError, error }
}


export type ValidationWarning = {
    readonly tag: Tags.validationWarning
    readonly warning: string
}

export function makeValidationWarning(warning: string): ValidationWarning {
    return { tag: Tags.validationWarning, warning }
}
