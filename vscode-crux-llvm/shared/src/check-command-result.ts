interface CheckCommandSuccess {
    check: true
    output: string
}

interface CheckCommandFailure {
    check: false
    errorMessage: string
}

export type CheckCommandResult = CheckCommandSuccess | CheckCommandFailure
