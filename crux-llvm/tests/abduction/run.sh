#!/bin/bash

echo "Running tests for 3 minutes each"
echo ""



echo "8-bit tests"

echo "abdpaper"
time timeout 180 crux-llvm --solver=cvc5 --get-abducts 3 --online-solver-output=./smtFiles8bitCvc52/test-abdpaper-8-abd.smt2 ./cFiles8bit/test-abdpaper-8.c
echo ""

echo "addident"
time timeout 180 crux-llvm --solver=cvc5 --get-abducts 3 --online-solver-output=./smtFiles8bitCvc52/test-addident-8-abd.smt2 ./cFiles8bit/test-addident-8.c
echo ""

echo "addinv"
time timeout 180 crux-llvm --solver=cvc5 --get-abducts 3 --online-solver-output=./smtFiles8bitCvc52/test-addinv-8-abd.smt2 ./cFiles8bit/test-addinv-8.c
echo ""

echo "andex"
time timeout 180 crux-llvm --solver=cvc5 --get-abducts 3 --online-solver-output=./smtFiles8bitCvc52/test-andex-8-abd.smt2 ./cFiles8bit/test-andex-8.c
echo ""

echo "file"
time timeout 180 crux-llvm --solver=cvc5 --get-abducts 3 --online-solver-output=./smtFiles8bitCvc52/test-file-8-abd.smt2 ./cFiles8bit/test-file-8.c
echo ""

echo "maxint"
time timeout 180 crux-llvm --solver=cvc5 --get-abducts 3 --online-solver-output=./smtFiles8bitCvc52/test-maxint-8-abd.smt2 ./cFiles8bit/test-maxint-8.c
echo ""

echo "multident"
time timeout 180 crux-llvm --solver=cvc5 --get-abducts 3 --online-solver-output=./smtFiles8bitCvc52/test-multident-8-abd.smt2 ./cFiles8bit/test-multident-8.c
echo ""

echo "multinv"
time timeout 180 crux-llvm --solver=cvc5 --get-abducts 3 --online-solver-output=./smtFiles8bitCvc52/test-multinv-8-abd.smt2 ./cFiles8bit/test-multinv-8.c
echo ""

echo "trans"
time timeout 180 crux-llvm --solver=cvc5 --get-abducts 3 --online-solver-output=./smtFiles8bitCvc52/test-trans-8-abd.smt2 ./cFiles8bit/test-trans-8.c
echo ""



echo "32-bit tests"

echo "abdpaper"
time timeout 180 crux-llvm --solver=cvc5 --get-abducts 3 --online-solver-output=./smtFiles32bitCvc52/test-abdpaper-32-abd.smt2 ./cFiles32bit/test-abdpaper-32.c
echo ""

echo "addident"
time timeout 180 crux-llvm --solver=cvc5 --get-abducts 3 --online-solver-output=./smtFiles32bitCvc52/test-addident-32-abd.smt2 ./cFiles32bit/test-addident-32.c
echo ""

echo "addinv"
time timeout 180 crux-llvm --solver=cvc5 --get-abducts 3 --online-solver-output=./smtFiles32bitCvc52/test-addinv-32-abd.smt2 ./cFiles32bit/test-addinv-32.c
echo ""

echo "andex"
time timeout 180 crux-llvm --solver=cvc5 --get-abducts 3 --online-solver-output=./smtFiles32bitCvc52/test-andex-32-abd.smt2 ./cFiles32bit/test-andex-32.c
echo ""

echo "file"
time timeout 180 crux-llvm --solver=cvc5 --get-abducts 3 --online-solver-output=./smtFiles32bitCvc52/test-file-32-abd.smt2 ./cFiles32bit/test-file-32.c
echo ""

echo "maxint"
time timeout 180 crux-llvm --solver=cvc5 --get-abducts 3 --online-solver-output=./smtFiles32bitCvc52/test-maxint-32-abd.smt2 ./cFiles32bit/test-maxint-32.c
echo ""

echo "multident"
time timeout 180 crux-llvm --solver=cvc5 --get-abducts 3 --online-solver-output=./smtFiles32bitCvc52/test-multident-32-abd.smt2 ./cFiles32bit/test-multident-32.c
echo ""

echo "multinv"
time timeout 180 crux-llvm --solver=cvc5 --get-abducts 3 --online-solver-output=./smtFiles32bitCvc52/test-multinv-32-abd.smt2 ./cFiles32bit/test-multinv-32.c
echo ""

echo "trans"
time timeout 180 crux-llvm --solver=cvc5 --get-abducts 3 --online-solver-output=./smtFiles32bitCvc52/test-trans-32-abd.smt2 ./cFiles32bit/test-trans-32.c
echo ""