//@ts-check

'use strict'

import * as path from 'path'

import * as CopyWebpackPlugin from 'copy-webpack-plugin'
import { TsconfigPathsPlugin } from 'tsconfig-paths-webpack-plugin'
import { Configuration } from 'webpack'

const sharedOutput: Configuration['output'] = {
    devtoolModuleFilenameTemplate: '../[resource-path]',
    filename: '[name].bundle.js',
    path: path.resolve(__dirname, 'dist'),
}

const sharedConfiguration: Configuration = {

    devtool: 'source-map',

    externals: {
        vscode: 'commonjs vscode',
    },

    mode: 'development',

    module: {
        rules: [

            {
                test: /\.css$/,
                use: [
                    'style-loader',
                    'webpack-typings-for-css',
                    {
                        loader: 'css-loader',
                        options: {
                            modules: {
                                localIdentName: '[name]__[local]__[hash:base64]',
                            },
                        },
                    },
                ],
            },

            {
                test: /\.tsx?$/,
                exclude: /node_modules/,
                use: {
                    loader: 'ts-loader',
                    options: {
                        projectReferences: true,
                    },
                },
            },

        ],
    },

    plugins: [
        new CopyWebpackPlugin({
            patterns: [
                { from: 'webview/node_modules/vscode-codicons/dist', to: 'vscode-codicons' },
                { from: 'static', to: 'static' },
            ],
        }),
    ],

    resolve: {
        extensions: ['.ts', '.tsx', '.js'],
        plugins: [new TsconfigPathsPlugin({
            // Options: https://www.npmjs.com/package/tsconfig-paths-webpack-plugin
            logLevel: 'INFO',
        })],
    },

    target: 'node',

}

const config: Configuration[] = [

    (Object.assign({

        entry: {
            client: './client/src/extension.ts',
            server: './server/src/server.ts',
        },

        output: Object.assign({
            library: {
                type: 'commonjs2',
            },
        }, sharedOutput),

    }, sharedConfiguration)),

    (Object.assign({

        entry: {
            webview: './webview/src/webview.tsx',
        },

        output: Object.assign({
            library: {
                // not sure this is correct, but it definitely cannot be
                // 'commonjs2' as the extension raises an exception when seeing
                // 'modules.export = ...'
                type: 'window',
            },
        }, sharedOutput),

    }, sharedConfiguration)),

]

module.exports = config
