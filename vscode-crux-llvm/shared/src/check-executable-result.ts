interface CheckExecutableSuccess {
    check: true
    output: string
}

interface CheckExecutableFailure {
    check: false
    errorMessage: string
}

export type CheckExecutableResult = CheckExecutableSuccess | CheckExecutableFailure
