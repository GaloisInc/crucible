import * as vscode from 'vscode'

import { Configuration, ConfigurationKeys } from '@shared/configuration'
import * as Constants from '@shared/constants'


export function getConfiguration(): vscode.WorkspaceConfiguration {
    return vscode.workspace.getConfiguration(Constants.settingsName)
}


export function fromWorkspaceConfiguration(
    configuration: vscode.WorkspaceConfiguration,
): Configuration {
    return {
        [ConfigurationKeys.CruxLLVM]: configuration.get(ConfigurationKeys.CruxLLVM) || '',
        [ConfigurationKeys.Clang]: configuration.get(ConfigurationKeys.Clang) || '',
        [ConfigurationKeys.Debug]: configuration.get(ConfigurationKeys.Debug) || '',
        [ConfigurationKeys.IncludeDirs]: configuration.get(ConfigurationKeys.IncludeDirs) || [],
        [ConfigurationKeys.LLVMLink]: configuration.get(ConfigurationKeys.LLVMLink) || '',
        [ConfigurationKeys.PATH]: configuration.get(ConfigurationKeys.PATH) || '',
    }
}
