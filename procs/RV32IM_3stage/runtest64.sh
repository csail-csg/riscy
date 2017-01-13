#!/bin/bash

# Copyright (c) 2016, 2017 Massachusetts Institute of Technology

# Permission is hereby granted, free of charge, to any person
# obtaining a copy of this software and associated documentation
# files (the "Software"), to deal in the Software without
# restriction, including without limitation the rights to use, copy,
# modify, merge, publish, distribute, sublicense, and/or sell copies
# of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:

# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
# BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
# ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
# CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

if [ -d $RISCY_TOOLS/riscv64-unknown-elf/share/riscv-tests/isa ] ; then
    TEST_DIR="$RISCY_TOOLS/riscv64-unknown-elf/share/riscv-tests/isa"
elif [ -d $RISCY_TOOLS/riscv32-unknown-elf/share/riscv-tests/isa ] ; then
    TEST_DIR="$RISCY_TOOLS/riscv32-unknown-elf/share/riscv-tests/isa"
else
    echo "[ERROR] Can't find tests in \"$RISCY_TOOLS/riscv[32|64]-unknown-elf/share/riscv-tests/isa"
    return 1
fi

if [ "$#" -eq 0 ] ; then
    echo "Please select a set of tests:"
    echo "0) full test suite"
    echo ""
    echo "    sanity checks:"
    echo "1) rv64ui-mcu-add"
    echo ""
    echo "    im tests:"
    echo "2) rv64ui-mcu-*"
    echo "3) rv64um-mcu-*"
    echo ""
    echo "    privilege tests:"
    echo "4) rv64mi-mcu-*"
    echo "5) rv64si-mcu-*"
    read OPTION
else
    OPTION=$1
fi

RUNEXE="./verilator/bin/ubuntu.exe --just-run"

rm -rf out/
mkdir -p out

case "$OPTION" in
    0) files=`find $TEST_DIR/rv64ui-mcu-* -type f ! -name "*.*"`
       files="$files "`find $TEST_DIR/rv64um-mcu-* -type f ! -name "*.*"`
       files="$files "`find $TEST_DIR/rv64mi-mcu-* -type f ! -name "*.*"`
       files="$files "`find $TEST_DIR/rv64si-mcu-* -type f ! -name "*.*"`
       ;;
    1) $RUNEXE $TEST_DIR/rv64ui-mcu-add
       files=
       ;;
    2) files=`find $TEST_DIR/rv64ui-mcu-* -type f ! -name "*.*"`
       ;;
    3) files=`find $TEST_DIR/rv64um-mcu-* -type f ! -name "*.*"`
       ;;
    4) files=`find $TEST_DIR/rv64mi-mcu-* -type f ! -name "*.*"`
       ;;
    5) files=`find $TEST_DIR/rv64si-mcu-* -type f ! -name "*.*"`
       ;;
    *) echo "Invalid Test Code"
       exit
       ;;
esac

for hexfile in $files ; do
    basehexfile=$(basename "$hexfile")
    $RUNEXE $hexfile &> out/${basehexfile}.out
    # check return value
    errorcode=$?
    if [ $errorcode -ne 0 ] ; then
        grep ERROR out/${basehexfile}.out > /dev/null
        if [ $? -eq 0 ] ; then
            echo "$basehexfile FAILED $errorcode" # with divergence
        else
            echo "$basehexfile FAILED $errorcode (without divergence)"
        fi
        # exit 1
    else
        grep ERROR out/${basehexfile}.out > /dev/null
        if [ $? -eq 0 ] ; then
            echo "$basehexfile PASSED (with divergence)"
        else
            echo "$basehexfile OK"
        fi
    fi
done
rm SOCK.*
