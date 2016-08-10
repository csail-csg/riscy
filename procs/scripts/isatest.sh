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
    echo "ERROR: RUN_EXE should be passed as a command line argument"
    exit 1
else
    RUN_EXE=$1
fi

rm -rf out/
mkdir -p out

# All the assembly files
files=`find $RISCY_TOOLS/riscv64-unknown-elf/share/riscv-tests/isa/rv64ui-p-* -type f ! -name "*.*"`
files="$files "`find $RISCY_TOOLS/riscv64-unknown-elf/share/riscv-tests/isa/rv64um-p-* -type f ! -name "*.*"`
files="$files "`find $RISCY_TOOLS/riscv64-unknown-elf/share/riscv-tests/isa/rv64ua-p-* -type f ! -name "*.*"`
files="$files "`find $RISCY_TOOLS/riscv64-unknown-elf/share/riscv-tests/isa/rv64uf-p-* -type f ! -name "*.*"`
files="$files "`find $RISCY_TOOLS/riscv64-unknown-elf/share/riscv-tests/isa/rv64ud-p-* -type f ! -name "*.*"`
files="$files "`find $RISCY_TOOLS/riscv64-unknown-elf/share/riscv-tests/isa/rv64mi-p-* -type f ! -name "*.*"`
files="$files "`find $RISCY_TOOLS/riscv64-unknown-elf/share/riscv-tests/isa/rv64si-p-* -type f ! -name "*.*"`

for hexfile in $files ; do
    basehexfile=$(basename "$hexfile")
    $RUN_EXE $hexfile &> out/${basehexfile}.out
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
