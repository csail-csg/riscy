#!/bin/bash

# Copyright (c) 2017 Massachusetts Institute of Technology

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

print_usage()
{
    echo "Usage: $0 [<elf-file>]"
    echo ""
    echo "This script generates the necessary hex file from the provided ELF file."
    echo "If no elf file is provided, then this script uses the test rv64ui-p-add"
    echo "as a default program."
    echo ""
    echo "Note: This script requires RISCY_HOME to be defined"
}

if [ "$1" = "-h" ] || [ "$1" = "--help" ] ; then
    print_usage
    exit 0
fi

if [ ! -d $RISCY_HOME/tools/elf2hex ] ; then
    echo "[ERROR] Can't find folder \$RISCY_HOME/tools/elf2hex, check if RISCY_HOME is defined"
    exit 1
fi

if [ ! -f $RISCY_HOME/tools/elf2hex/elf2hex ] ; then
    echo "[INFO] Compiling elf2hex binary"
    make -C $RISCY_HOME/tools/elf2hex
    if [ ! -f $RISCY_HOME/tools/elf2hex/elf2hex ] ; then
        echo "[ERROR] Compilation failed"
        exit 1
    fi
fi

if [ $# -eq 0 ] ; then
    ELF_FILE=$RISCY_TOOLS/riscv64-unknown-elf/share/riscv-tests/isa/rv64ui-p-add
else
    ELF_FILE=$1
fi

if [ ! -f $ELF_FILE ] ; then
    echo "[ERROR] Can't find elf file $ELF_FILE"
    exit 1
fi

# Make ram.hex for this processor
$RISCY_HOME/tools/elf2hex/elf2hex $ELF_FILE 0x80000000 256K ram.hex
