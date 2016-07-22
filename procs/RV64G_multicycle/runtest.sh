#!/bin/bash

# Copyright (c) 2016 Massachusetts Institute of Technology

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

if [ "$#" -eq 0 ] ; then
    echo "Please select a set of tests:"
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
    read OPTION
else
    OPTION=$1
fi

RUNEXE=./verilator/bin/ubuntu.exe

rm -rf out/
mkdir -p out

case "$OPTION" in
    1) $RUNEXE $RISCY_TOOLS/riscv64-unknown-elf/share/riscv-tests/isa/rv64ui-p-add
       files=
       ;;
    2) files=`find $RISCY_TOOLS/riscv64-unknown-elf/share/riscv-tests/isa/rv64ui-p-* -type f ! -name "*.*"`
       ;;
    3) files=`find $RISCY_TOOLS/riscv64-unknown-elf/share/riscv-tests/isa/rv64um-p-* -type f ! -name "*.*"`
       ;;
    4) files=`find $RISCY_TOOLS/riscv64-unknown-elf/share/riscv-tests/isa/rv64ua-p-* -type f ! -name "*.*"`
       ;;
    5) files=`find $RISCY_TOOLS/riscv64-unknown-elf/share/riscv-tests/isa/rv64uf-p-* -type f ! -name "*.*"`
       ;;
    6) files=`find $RISCY_TOOLS/riscv64-unknown-elf/share/riscv-tests/isa/rv64ud-p-* -type f ! -name "*.*"`
       ;;
    7) files=`find $RISCY_TOOLS/riscv64-unknown-elf/share/riscv-tests/isa/rv64mi-p-* -type f ! -name "*.*"`
       ;;
    8) files=`find $RISCY_TOOLS/riscv64-unknown-elf/share/riscv-tests/isa/rv64si-p-* -type f ! -name "*.*"`
       ;;
    *) echo "Invalid Test Code"
       exit
       ;;
esac

for hexfile in $files ; do
    basehexfile=$(basename "$hexfile")
    ./verilator/bin/ubuntu.exe $hexfile &> out/${basehexfile}.out
    # check return value
    errorcode=$?
    if [ $errorcode -ne 0 ] ; then
        grep ERROR out/${basehexfile}.out > /dev/null
        if [ $errorcode -ne 0 ] ; then
            echo "$basehexfile FAILED $errorcode" # with divergence
        else
            echo "$basehexfile FAILED $errorcode (without divergence)"
        fi
        # exit 1
    else
        grep ERROR out/${basehexfile}.out > /dev/null
        if [ $errorcode -ne 0 ] ; then
            echo "$basehexfile PASSED (with divergence)"
        else
            echo "$basehexfile OK"
        fi
    fi
done
rm SOCK.*
