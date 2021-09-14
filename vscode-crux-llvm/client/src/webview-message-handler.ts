import { UnreachableCaseError } from 'ts-essentials'
import * as ls from 'vscode-languageclient/node'

import * as LSPExtensions from '@shared/lsp-extensions'
import * as W2E from '@shared/webview-to-extension'

export const makeHandler =
    (
        client: ls.LanguageClient,
    ) =>
        (message: W2E.Message): void => {

            switch (message.tag) {

                case W2E.Tags.abortCruxLLVM: {
                    client.sendNotification(LSPExtensions.abortCruxLLVM)
                    break
                }

                default: {
                    throw new UnreachableCaseError(message.tag)
                }

            }

        }
