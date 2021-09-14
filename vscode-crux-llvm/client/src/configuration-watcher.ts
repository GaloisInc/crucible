import * as vscode from 'vscode'

import { checkExecutable } from '@shared/check-executable'
import { ConfigurationKeys, KeyOfExecutable } from '@shared/configuration'
import * as Constants from '@shared/constants'
import * as E2W from '@shared/extension-to-webview'

import * as Configuration from './configuration'


export const onDidChangeConfiguration =
    (
        webviewView: vscode.WebviewView,
    ) =>
        (e: vscode.ConfigurationChangeEvent): void => {

            if (e.affectsConfiguration(Constants.settingsName)) {

                const configuration = Configuration.getConfiguration()

                webviewView.webview.postMessage({
                    tag: E2W.Tags.configurationChanged,
                    // WARNING: the following code is **not** type-safe, handle with caution!
                    newConfiguration: Configuration.fromWorkspaceConfiguration(configuration),
                } as E2W.Message)
            }

            const postMessageIfAffected =
                (
                    field: KeyOfExecutable,
                    messageTag: E2W.Tags,
                ) => {
                    if (e.affectsConfiguration(`${Constants.settingsName}.${field}`)) {
                        const newStatus = checkExecutable(
                            Configuration.fromWorkspaceConfiguration(Configuration.getConfiguration()),
                            field,
                        )
                        webviewView.webview.postMessage({
                            tag: messageTag,
                            status: newStatus,
                        } as E2W.Message)
                    }
                }

            postMessageIfAffected(
                ConfigurationKeys.Clang,
                E2W.Tags.statusOfClang,
            )

            postMessageIfAffected(
                ConfigurationKeys.CruxLLVM,
                E2W.Tags.statusOfCruxLLVM,
            )

            postMessageIfAffected(
                ConfigurationKeys.LLVMLink,
                E2W.Tags.statusOfLLVMLink,
            )

        }
