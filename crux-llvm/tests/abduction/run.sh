#!/bin/bash

echo "Running tests for 3 minutes each"
echo ""



echo "8-bit tests"

echo "abdpaper"
timeout 180 crux-llvm --solver=cvc5 --online-solver-output=./smtFiles8bitCvc5/test-abdpaper-8-abd.smt2 ./cFiles8bit/test-abdpaper-8.c
echo ""

echo "addident"
timeout 180 crux-llvm --solver=cvc5 --online-solver-output=./smtFiles8bitCvc5/test-addident-8-abd.smt2 ./cFiles8bit/test-addident-8.c
echo ""

echo "addinv"
timeout 180 crux-llvm --solver=cvc5 --online-solver-output=./smtFiles8bitCvc5/test-addinv-8-abd.smt2 ./cFiles8bit/test-addinv-8.c
echo ""

echo "andex"
timeout 180 crux-llvm --solver=cvc5 --online-solver-output=./smtFiles8bitCvc5/test-andex-8-abd.smt2 ./cFiles8bit/test-andex-8.c
echo ""

echo "file"
timeout 180 crux-llvm --solver=cvc5 --online-solver-output=./smtFiles8bitCvc5/test-file-8-abd.smt2 ./cFiles8bit/test-file-8.c
echo ""

echo "maxint"
timeout 180 crux-llvm --solver=cvc5 --online-solver-output=./smtFiles8bitCvc5/test-maxint-8-abd.smt2 ./cFiles8bit/test-maxint-8.c
echo ""

echo "multident"
timeout 180 crux-llvm --solver=cvc5 --online-solver-output=./smtFiles8bitCvc5/test-multident-8-abd.smt2 ./cFiles8bit/test-multident-8.c
echo ""

echo "multinv"
timeout 180 crux-llvm --solver=cvc5 --online-solver-output=./smtFiles8bitCvc5/test-multinv-8-abd.smt2 ./cFiles8bit/test-multinv-8.c
echo ""

echo "trans"
timeout 180 crux-llvm --solver=cvc5 --online-solver-output=./smtFiles8bitCvc5/test-trans-8-abd.smt2 ./cFiles8bit/test-trans-8.c
echo ""



echo "32-bit tests"

echo "abdpaper"
timeout 180 crux-llvm --solver=cvc5 --online-solver-output=./smtFiles32bitCvc5/test-abdpaper-32-abd.smt2 ./cFiles32bit/test-abdpaper-32.c
echo ""

echo "addident"
timeout 180 crux-llvm --solver=cvc5 --online-solver-output=./smtFiles32bitCvc5/test-addident-32-abd.smt2 ./cFiles32bit/test-addident-32.c
echo ""

echo "addinv"
timeout 180 crux-llvm --solver=cvc5 --online-solver-output=./smtFiles32bitCvc5/test-addinv-32-abd.smt2 ./cFiles32bit/test-addinv-32.c
echo ""

echo "andex"
timeout 180 crux-llvm --solver=cvc5 --online-solver-output=./smtFiles32bitCvc5/test-andex-32-abd.smt2 ./cFiles32bit/test-andex-32.c
echo ""

echo "file"
timeout 180 crux-llvm --solver=cvc5 --online-solver-output=./smtFiles32bitCvc5/test-file-32-abd.smt2 ./cFiles32bit/test-file-32.c
echo ""

echo "maxint"
timeout 180 crux-llvm --solver=cvc5 --online-solver-output=./smtFiles32bitCvc5/test-maxint-32-abd.smt2 ./cFiles32bit/test-maxint-32.c
echo ""

echo "multident"
timeout 180 crux-llvm --solver=cvc5 --online-solver-output=./smtFiles32bitCvc5/test-multident-32-abd.smt2 ./cFiles32bit/test-multident-32.c
echo ""

echo "multinv"
timeout 180 crux-llvm --solver=cvc5 --online-solver-output=./smtFiles32bitCvc5/test-multinv-32-abd.smt2 ./cFiles32bit/test-multinv-32.c
echo ""

echo "trans"
timeout 180 crux-llvm --solver=cvc5 --online-solver-output=./smtFiles32bitCvc5/test-trans-32-abd.smt2 ./cFiles32bit/test-trans-32.c
echo ""