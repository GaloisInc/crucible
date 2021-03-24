//@ts-check

'use strict'

import * as path from 'path'

// import * as CopyWebpackPlugin from 'copy-webpack-plugin'
import { TsconfigPathsPlugin } from 'tsconfig-paths-webpack-plugin'
import { Configuration } from 'webpack'

const config: Configuration = {

    devtool: 'source-map',

    entry: {
        client: './client/src/extension.ts',
        server: './server/src/server.ts',
        webview: './webview/src/webview.tsx',
    },

    externals: {
        vscode: 'commonjs vscode',
    },

    mode: 'development',

    module: {
        rules: [
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

    output: {
        devtoolModuleFilenameTemplate: '../[resource-path]',
        filename: '[name].bundle.js',
        libraryTarget: 'commonjs2',
        path: path.resolve(__dirname, 'dist'),
    },

    plugins: [
        // new CopyWebpackPlugin({
        //     // patterns: [
        //     //     { from: 'static', to: 'static' },
        //     // ],
        // }),
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

module.exports = config
