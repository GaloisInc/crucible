/**
 * Dispatching logic for all crux-llvm log entries we care to act upon
 * receiving.
 */

import update from 'immutability-helper'
import { UnreachableCaseError } from 'ts-essentials'

import * as ExtensionToWebview from '@shared/extension-to-webview'
import { ReactSetter } from '@shared/types'

import { Goal, GoalStatus } from './goals'


export function handleCruxLLVMLog(
    setters: {
        setGoals: ReactSetter<Goal[]>,
    },
    message: ExtensionToWebview.CruxLLVMLogEntry,
): void {
    const logEntry = message.logEntry

    switch (logEntry.tag) {

        case 'LoggingCrux': {
            handleCruxLogEntry(setters, logEntry.contents)
            break
        }

        case 'LoggingCruxLLVM': {
            break
        }

        default: {
            new UnreachableCaseError(logEntry)
        }

    }
}


function handleCruxLogEntry(
    setters: {
        setGoals: ReactSetter<Goal[]>,
    },
    cruxLogEntry: CruxLogMessage,
) {

    switch (cruxLogEntry.tag) {

        case 'EndedGoal': {
            const goalNumber = cruxLogEntry.contents
            setters.setGoals(goals => {
                if (goalNumber >= goals.length) {
                    /**
                     * This may happen as a consequence of having started to
                     * work on a different (shorter) set of goals while still
                     * processing messages from a previous (longer) set of
                     * goals.
                     *
                     * This means there is missing logic somewhere to abort or
                     * ignore messages from the previous set of goals.
                     */
                    console.log('Attempting to update goals beyond its length, ignoring.')
                    return goals
                }
                return update(
                    goals,
                    { [goalNumber]: { status: { $set: GoalStatus.GoalEnded } } },
                )
            })
            break
        }

        case 'ProofObligations': {
            const goals = cruxLogEntry.contents
            setters.setGoals(
                goals.map(({ labeledPred, labeledPredMsg }) => ({
                    labeledPred,
                    labeledPredMsg,
                    status: GoalStatus.GoalCreated,
                })),
            )
            break
        }

        case 'StartedGoal': {
            const goalNumber = cruxLogEntry.contents
            setters.setGoals(goals =>
                update(
                    goals,
                    { [goalNumber]: { status: { $set: GoalStatus.GoalStarted } } },
                ),
            )
            break
        }

        case 'AttemptingProvingVCs':
        case 'Checking':
        case 'DisablingBranchCoverageRequiresPathSatisfiability':
        case 'DisablingProfilingIncompatibleWithPathSplitting':
        case 'FoundCounterExample':
        case 'Help':
        case 'PathsUnexplored':
        case 'SimulationComplete':
        case 'SimulationTimedOut':
        case 'TotalPathsExplored':
        case 'SkippingUnsatCoresBecauseMCSatEnabled':
        case 'UnsupportedTimeoutFor':
        case 'Version':
            {
                break
            }

        default: {
            new UnreachableCaseError(cruxLogEntry)
        }
    }

}
