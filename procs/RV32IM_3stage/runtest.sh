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

SKIP_TESTS="rv32mi-mcu-dirty rv32mi-mcu-scall"

print_usage ()
{
    echo "Usage: $0 [<backend-id> [<test-id>]]"
    echo ""
    echo "This script runs a selection of riscv-tests on the current processor."
    echo "backend-id and test-id are the values from the menus that appear when"
    echo "no command line arguments are provided."
}

run_connectal ()
{
    hexfile=$1
    basehexfile=$(basename "$hexfile")

    # run the processor
    ./verilator/bin/ubuntu.exe --just-trace $hexfile &> out/${basehexfile}.out
}

run_verilator ()
{
    hexfile=$1
    basehexfile=$(basename "$hexfile")

    # generate hex file
    ./genhex.sh $hexfile

    # and run the processor
    ./RV32IM_3stage.exe &> out/${basehexfile}.out
}

if [ "$1" = "-h" ] || [ "$1" = "--help" ] ; then
    print_usage
    exit 0
fi

# make sure test directory exists
if [ ! -d $RISCY_TOOLS ] ; then
    echo "[ERROR] Can't find directory RISCY_TOOLS=\"${RISCY_TOOLS}\""
    exit 1
elif [ -d $RISCY_TOOLS/riscv32-unknown-elf/share/riscv-tests/isa ] ; then
    TEST_DIR=$RISCY_TOOLS/riscv32-unknown-elf/share/riscv-tests/isa
elif [ -d $RISCY_TOOLS/riscv64-unknown-elf/share/riscv-tests/isa ] ; then
    TEST_DIR=$RISCY_TOOLS/riscv64-unknown-elf/share/riscv-tests/isa
else
    echo "[ERROR] Can't find test directory in \"${RISCY_TOOLS}\""
    exit 1
fi

if [ "$#" -gt 0 ] ; then
    BACKEND=$1
else
    echo "Please select a backend:"
    echo "0) connectal (verilator)"
    echo "1) verilator"
    read BACKEND
fi

# Validate backend choice
case "$BACKEND" in
    0) ;;
    1) ;;
    *) echo "[ERROR] Invalid Backend Code"
       exit 1
       ;;
esac

if [ "$#" -gt 1 ] ; then
    TESTS=$2
else
    echo "Please select a set of tests:"
    echo "0) full test suite"
    echo ""
    echo "    sanity checks:"
    echo "1) rv32ui-mcu-add"
    echo ""
    echo "    im tests:"
    echo "2) rv32ui-mcu-*"
    echo "3) rv32um-mcu-*"
    echo ""
    echo "    privilege tests:"
    echo "4) rv32mi-mcu-*"
    echo "5) rv32si-mcu-*"
    read TESTS
fi

case "$TESTS" in
    0) files=`find $TEST_DIR/rv32ui-mcu-* -type f ! -name "*.*"`
       files="$files "`find $TEST_DIR/rv32um-mcu-* -type f ! -name "*.*"`
       files="$files "`find $TEST_DIR/rv32mi-mcu-* -type f ! -name "*.*"`
       files="$files "`find $TEST_DIR/rv32si-mcu-* -type f ! -name "*.*"`
       ;;
    1) files=$TEST_DIR/rv32ui-mcu-add
       ;;
    2) files=`find $TEST_DIR/rv32ui-mcu-* -type f ! -name "*.*"`
       ;;
    3) files=`find $TEST_DIR/rv32um-mcu-* -type f ! -name "*.*"`
       ;;
    4) files=`find $TEST_DIR/rv32mi-mcu-* -type f ! -name "*.*"`
       ;;
    5) files=`find $TEST_DIR/rv32si-mcu-* -type f ! -name "*.*"`
       ;;
    *) echo "[ERROR] Invalid Test Code"
       exit 1
       ;;
esac

rm -rf out/
mkdir -p out

EXIT_CODE=0

for hexfile in $files ; do
    basehexfile=$(basename "$hexfile")

    # skip some tests
    SKIP=0
    for skippedtest in $SKIP_TESTS ; do
        if [ "$basehexfile" == "$skippedtest" ] ; then
            echo "$basehexfile SKIPPED"
            SKIP=1
        fi
    done
    if [ $SKIP -eq 1 ] ; then
        continue
    fi

    # run processor
    case "$BACKEND" in
        0) run_connectal $hexfile
           ;;
        1) run_verilator $hexfile
           ;;
        *) echo "[ERROR] Invalid Backend Code"
           exit 1
           ;;
    esac

    # check results
    grep PASSED out/${basehexfile}.out > /dev/null
    if [ $? -ne 0 ] ; then
        errorcode=`grep FAILED out/${basehexfile}.out`
        if [ $? -ne 0 ] ; then
            # neither PASSED nor FAILED were found in the output
            echo "$basehexfile ERROR (neither pass nor fail)"
        else
            # This will print FAILED from the error code
            echo "$basehexfile $errorcode"
            EXIT_CODE=1
        fi
    else
        echo "$basehexfile OK"
    fi
done

rm -f SOCK.*

exit $EXIT_CODE
