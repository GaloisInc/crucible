/**
 * Data structures we use to represent proof obligations data in the webview.
 */

import { UnreachableCaseError } from 'ts-essentials'


export enum GoalStatus {
    GoalAborted,
    GoalCreated,
    GoalStarted,
    GoalDone,
}


export function showGoalStatus(s: GoalStatus): string {
    switch (s) {
        case GoalStatus.GoalAborted: return 'Aborted'
        case GoalStatus.GoalCreated: return 'Ready'
        case GoalStatus.GoalStarted: return 'Proving...'
        case GoalStatus.GoalDone: return 'Done'
        default: throw new UnreachableCaseError(s)
    }
}


export interface Goal {
    labeledPred: string
    labeledPredMsg: string
    status: GoalStatus,
}


export function abortedIfNotDone(status: GoalStatus): GoalStatus {
    switch (status) {
        case GoalStatus.GoalAborted: return GoalStatus.GoalAborted
        case GoalStatus.GoalCreated: return GoalStatus.GoalAborted
        case GoalStatus.GoalStarted: return GoalStatus.GoalAborted
        case GoalStatus.GoalDone: return GoalStatus.GoalDone
        default: throw new UnreachableCaseError(status)
    }
}
