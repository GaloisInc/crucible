import * as LanguageServer from 'vscode-languageserver'

const COUNTER_EXAMPLE = 'counter-example'
const ASSUMPTIONS = 'assumptions'

function severityOf(s: string): LanguageServer.DiagnosticSeverity {
    switch (s) {
        case 'ok': {
            return LanguageServer.DiagnosticSeverity.Information
        }
        case 'fail': {
            return LanguageServer.DiagnosticSeverity.Error
        }
        case 'unknown': {
            return LanguageServer.DiagnosticSeverity.Warning
        }
        default: {
            throw new Error(`Unhandled severity: ${s}. Please report.`)
        }
    }
}

// Locations as they appear in the report
interface Location {
    col: string
    line: string
}

function positionFromLocation(location: Location): LanguageServer.Position {
    return LanguageServer.Position.create(
        parseInt(location.line) - 1,
        parseInt(location.col),
    )
}

function mainDiagnostic(object: MainDiagnostic): LanguageServer.Diagnostic {
    const position = positionFromLocation(object.location)
    const message = (
        ('details-long' in object && object['details-long'])
            ? object['details-long']
            : (
                ('details-short' in object && object['details-short'])
                    ? object['details-short']
                    : 'No details for this diagnostic. Please report.'
            )
    )
    return {
        message,
        range: {
            start: position,
            end: position,
        },
        severity: severityOf(object.status),
        source: 'crux-llvm',
    }
}

type CounterExampleDiagnostic = {
    bits: string
    loc: Location
    name: string
    val: string
}

function counterExampleDiagnostic(
    object: CounterExampleDiagnostic,
): LanguageServer.Diagnostic {
    const position = positionFromLocation(object.loc)
    const message = `Counter-example: ${object.name} = ${object.val} (as an ${object.bits}-bit value)`
    return {
        message,
        range: {
            start: position,
            end: position,
        },
        severity: LanguageServer.DiagnosticSeverity.Error,
        source: 'crux-llvm',
    }
}

type AssumptionDiagnostic = {
    loc: Location
    text: string
}

function assumptionDiagnostic(object: AssumptionDiagnostic): LanguageServer.Diagnostic {
    const position = positionFromLocation(object.loc)
    const message = `Assumption: ${object.text})`
    return {
        message,
        range: {
            start: position,
            end: position,
        },
        severity: LanguageServer.DiagnosticSeverity.Information,
        source: 'crux-llvm',
    }
}

export type MainDiagnostic = {
    'details-long'?: string
    'details-short'?: string
    location: Location
    status: string
    [ASSUMPTIONS]?: AssumptionDiagnostic[]
    [COUNTER_EXAMPLE]?: CounterExampleDiagnostic[]
}

/**
 * Turns a report into some array of diagnostics.
 * Assumptions will be listed next to code snippets.
 * @param object - one entry from report.json
 */
export function createDiagnostic(object: MainDiagnostic): LanguageServer.Diagnostic[] {
    return (
        [mainDiagnostic(object)]
            .concat(
                (object[COUNTER_EXAMPLE] || []).map(counterExampleDiagnostic),
                (object[ASSUMPTIONS] || []).map(assumptionDiagnostic),
            )
    )
}
