# vscode-crux-llvm

This extension allows VSCode to run `crux-llvm` in the background and report
diagnostics directly in the editor.

## Features

Diagnostics: When you open a C file, `crux-llvm` will attempt to check it.

## Requirements

You **must** have `crux-llvm`, a C compiler (such as `clang`), a linker (such as
`llvm-link`), and a solver (currently hardcoded to be `z3`) installed.

Configure the following extension settings so that the extension knows where to
find those.

## Extension Settings

This extension contributes the following settings:

* `crux-llvm.clang` (string): Path to the `clang` executable (e.g. `/path/to/clang`)

* `crux-llvm.crux-llvm` (string): Path to the `crux-llvm` executable (e.g.
  `/path/to/crux-llvm`)

* `crux-llvm.debug` (boolean): Set to true to make the extension output status
  information in the Visual Studio Code console

* `crux-llvm.llvm-link` (string): Path to the `llvm-link` executable (e.g.
  `/path/to/llvm-link`)

* `crux-llvm.path` (string): Unix `PATH` to use for finding solvers such as z3 (e.g.
  `/path/to/z3/bin/folder:/some/other/paths`)

## Known Issues

We are still working out some details of making sure the solvers time out
properly, and ironing out how error messages are located, phrased, and
displayed.

## Release Notes

### 0.0.1

Initial release of vscode-crux-llvm