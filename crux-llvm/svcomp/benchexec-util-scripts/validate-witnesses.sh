#!/usr/bin/env bash

set -xe

RUNDEFINITION=unreach-call

cd val_cpa-seq
PYTHONPATH=../benchexec python3 -m benchexec.benchexec -r SV-COMP21_${RUNDEFINITION} ../benchmark-defs/cpa-seq-validate-correctness-witnesses.xml
PYTHONPATH=../benchexec python3 -m benchexec.benchexec -r SV-COMP21_${RUNDEFINITION} ../benchmark-defs/cpa-seq-validate-violation-witnesses.xml
cd ..

cd val_cpa-witness2test
PYTHONPATH=../benchexec python3 -m benchexec.benchexec -r SV-COMP21_${RUNDEFINITION} ../benchmark-defs/cpa-witness2test-validate-violation-witnesses.xml
cd ..

cd val_fshell-witness2test
PYTHONPATH=../benchexec python3 -m benchexec.benchexec -r SV-COMP21_${RUNDEFINITION} ../benchmark-defs/fshell-witness2test-validate-violation-witnesses.xml
cd ..

cd val_metaval
PYTHONPATH=../benchexec python3 -m benchexec.benchexec -r SV-COMP21_${RUNDEFINITION} ../benchmark-defs/metaval-validate-correctness-witnesses.xml
PYTHONPATH=../benchexec python3 -m benchexec.benchexec -r SV-COMP21_${RUNDEFINITION} ../benchmark-defs/metaval-validate-violation-witnesses.xml
cd ..

cd val_nitwit
PYTHONPATH=../benchexec python3 -m benchexec.benchexec -r SV-COMP21_${RUNDEFINITION} ../benchmark-defs/nitwit-validate-violation-witnesses.xml
cd ..

cd val_uautomizer
PYTHONPATH=../benchexec python3 -m benchexec.benchexec -r SV-COMP21_${RUNDEFINITION} ../benchmark-defs/uautomizer-validate-correctness-witnesses.xml
PYTHONPATH=../benchexec python3 -m benchexec.benchexec -r SV-COMP21_${RUNDEFINITION} ../benchmark-defs/uautomizer-validate-violation-witnesses.xml
cd ..
