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

SKIP_TESTS="rv64ua-p-lrsc rv64mi-p-breakpoint rv64mi-p-scall"

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
    ./RV64G_multicycle.exe &> out/${basehexfile}.out
}

if [ "$1" = "-h" ] || [ "$1" = "--help" ] ; then
    print_usage
    exit 0
fi

# make sure test directory exists
if [ ! -d $RISCY_TOOLS ] ; then
    echo "[ERROR] Can't find directory RISCY_TOOLS=\"${RISCY_TOOLS}\""
    exit 1
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
    echo "1) rv64ui-p-add"
    echo ""
    echo "    imafd tests:"
    echo "2) rv64ui-p-*"
    echo "3) rv64um-p-*"
    echo "4) rv64ua-p-*"
    echo "5) rv64uf-p-*"
    echo "6) rv64ud-p-*"
    echo ""
    echo "    privilege tests:"
    echo "7) rv64mi-p-*"
    echo "8) rv64si-p-*"
    read TESTS
fi

case "$TESTS" in
    0) files=`find $TEST_DIR/rv64ui-p-* -type f ! -name "*.*"`
       files="$files "`find $TEST_DIR/rv64um-p-* -type f ! -name "*.*"`
       files="$files "`find $TEST_DIR/rv64ua-p-* -type f ! -name "*.*"`
       files="$files "`find $TEST_DIR/rv64uf-p-* -type f ! -name "*.*"`
       files="$files "`find $TEST_DIR/rv64ud-p-* -type f ! -name "*.*"`
       files="$files "`find $TEST_DIR/rv64mi-p-* -type f ! -name "*.*"`
       files="$files "`find $TEST_DIR/rv64si-p-* -type f ! -name "*.*"`
       ;;
    1) files=$TEST_DIR/rv64ui-p-add
       ;;
    2) files=`find $TEST_DIR/rv64ui-p-* -type f ! -name "*.*"`
       ;;
    3) files=`find $TEST_DIR/rv64um-p-* -type f ! -name "*.*"`
       ;;
    4) files=`find $TEST_DIR/rv64ua-p-* -type f ! -name "*.*"`
       ;;
    5) files=`find $TEST_DIR/rv64uf-p-* -type f ! -name "*.*"`
       ;;
    6) files=`find $TEST_DIR/rv64ud-p-* -type f ! -name "*.*"`
       ;;
    7) files=`find $TEST_DIR/rv64mi-p-* -type f ! -name "*.*"`
       ;;
    8) files=`find $TEST_DIR/rv64si-p-* -type f ! -name "*.*"`
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
    basehexfile=$(basename "$hexfile")
    grep PASSED out/${basehexfile}.out > /dev/null
    if [ $? -ne 0 ] ; then
        errorcode=`grep FAILED out/${basehexfile}.out`
        if [ $? -ne 0 ] ; then
            # neither PASSED nor FAILED were found in the output
            echo "$basehexfile ERROR (neither pass nor fail)"
            EXIT_CODE=1
        else
            # This will print FAILED from the error code
            echo "$basehexfile $errorcode"
        fi
    else
        echo "$basehexfile OK"
    fi
done

rm -f SOCK.*

exit $EXIT_CODE
