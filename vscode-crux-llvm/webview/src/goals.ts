/**
 * Data structures we use to represent proof obligations data in the webview.
 */

export enum GoalStatus {
    GoalCreated,
    GoalStarted,
    GoalEnded,
}

export function showGoalStatus(s: GoalStatus): string {
    switch (s) {
        case GoalStatus.GoalCreated: return 'Ready'
        case GoalStatus.GoalStarted: return 'Proving...'
        case GoalStatus.GoalEnded: return 'Done'
    }
}

export interface Goal {
    labeledPred: string
    labeledPredMsg: string
    status: GoalStatus,
}
