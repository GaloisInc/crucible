import * as ChildProcess from 'child_process'
import * as fs from 'fs'
import * as LanguageServer from 'vscode-languageserver'
import * as os from 'os'
import * as path from 'path'
import { Position } from 'vscode-languageserver'

const COUNTER_EXAMPLE: string = 'counter-example'
const ASSUMPTIONS: string = 'assumptions'

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
            throw `Unhandled severity: ${s}. Please report.`
        }
    }
}

// Locations as they appear in the report
interface Location {
    col: string,
    line: string,
}

function positionFromLocation(location: Location): LanguageServer.Position {
    return LanguageServer.Position.create(
        parseInt(location.line) - 1,
        parseInt(location.col),
    )
}

function mainDiagnostic(object: any): LanguageServer.Diagnostic {
    const position = positionFromLocation(object.location)
    const message = (
        ('details-long' in object)
            ? object['details-long']
            : (
                ('details-short' in object)
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

function counterExampleDiagnostic(object: any): LanguageServer.Diagnostic {
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

function assumptionDiagnostic(object: any): LanguageServer.Diagnostic {
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

/**
 * Turns a report into some array of diagnostics.
 * Assumptions will be listed next to code snippets.
 * @param object one entry from report.json
 */
export function createDiagnostic(object: any): LanguageServer.Diagnostic[] {
    return (
        [mainDiagnostic(object)]
            .concat(
                (
                    (COUNTER_EXAMPLE in object && object[COUNTER_EXAMPLE] !== null)
                        ? object[COUNTER_EXAMPLE].map(counterExampleDiagnostic)
                        : []
                ),
                (
                    (ASSUMPTIONS in object && object[ASSUMPTIONS] !== null)
                        ? object[ASSUMPTIONS].map(assumptionDiagnostic)
                        : []

                )
            )
    )

}