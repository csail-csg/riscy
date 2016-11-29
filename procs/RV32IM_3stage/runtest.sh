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
    echo "0) full test suite"
    echo ""
    echo "    sanity checks:"
    echo "1) rv32ui-p-add"
    echo ""
    echo "    im tests:"
    echo "2) rv32ui-p-*"
    echo "3) rv32um-p-*"
    echo ""
    echo "    privilege tests:"
    echo "4) rv32mi-p-*"
    echo "5) rv32si-p-*"
    read OPTION
else
    OPTION=$1
fi

RUNEXE="./verilator/bin/ubuntu.exe --just-trace"

rm -rf out/
mkdir -p out

case "$OPTION" in
    0) files=`find isa/rv32ui-p-* -type f ! -name "*.*"`
       files="$files "`find isa/rv32um-p-* -type f ! -name "*.*"`
       files="$files "`find isa/rv32mi-p-* -type f ! -name "*.*"`
       files="$files "`find isa/rv32si-p-* -type f ! -name "*.*"`
       ;;
    1) $RUNEXE isa/rv32ui-p-add
       files=
       ;;
    2) files=`find isa/rv32ui-p-* -type f ! -name "*.*"`
       ;;
    3) files=`find isa/rv32um-p-* -type f ! -name "*.*"`
       ;;
    4) files=`find isa/rv32mi-p-* -type f ! -name "*.*"`
       ;;
    5) files=`find isa/rv32si-p-* -type f ! -name "*.*"`
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
