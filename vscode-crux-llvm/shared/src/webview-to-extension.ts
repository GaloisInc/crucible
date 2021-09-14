export enum Tags {
    abortCruxLLVM = 'AbortCruxLLVM',
}


export type Message
    = AbortCruxLLVM


export interface AbortCruxLLVM {
    readonly tag: Tags.abortCruxLLVM
}
