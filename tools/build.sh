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

# Abort on error
set -e

if [ $# -eq 1 ] ; then
    ISA=$1
else
    # default ISA is RV64G
    ISA=RV64G
fi

if echo "$ISA" | grep -qE "^RV32" ; then
    XLEN=32
elif echo "$ISA" | grep -qE "^RV64" ; then
    XLEN=64
else
    echo "[ERROR] This script expects a RISC-V ISA string in all caps as an input"
    echo "example: $0 RV64IMAFDC"
    return 1
fi

case $ISA in
    "RV64G")        WITH_ARCH=" "                           ;;
    "RV64GC")       WITH_ARCH=" --with-arch=RV64IMAFDC "    ;;
    "RV32G")        WITH_ARCH=" --with-xlen=32 "            ;;
    "RV32GC")       WITH_ARCH=" --with-arch=RV32IMAFDC "    ;;
    "RV64IMAFD")    WITH_ARCH=" "                           ;;
    "RV32IMAFD")    WITH_ARCH=" --with-xlen=32 "            ;;
    *)              WITH_ARCH=" --with-arch=$ISA "          ;;
esac

echo "Building $ISA toolchain..."

STARTINGDIR=$PWD
export RISCV=$PWD/$ISA
export PATH=$RISCV/bin:$PATH
mkdir -p $RISCV

# Build riscv-gnu-toolchain
echo "Building riscv-gnu-toolchain..."
cd $RISCV
mkdir build-gnu-toolchain
cd build-gnu-toolchain
../../riscv-gnu-toolchain/configure --prefix=$RISCV $WITH_ARCH
make

# Rebuild newlib with -mcmodel=medany
echo "Rebuilding newlib..."
cd build-gcc-newlib/riscv$XLEN-unknown-elf/newlib
sed 's/^CFLAGS = /CFLAGS = -mcmodel=medany /' Makefile > Makefile.sed
mv Makefile.sed Makefile
make clean
make
make install

# Build riscv-tests
echo "Building riscv-tests..."
cd $RISCV
mkdir build-tests
cd build-tests
../../riscv-tests/configure --prefix=$RISCV/riscv$XLEN-unknown-elf --with-xlen=$XLEN
# This may fail since some riscv-tests require ISA extensions
# Also there is an issue with building 32-bit executables when gcc is
# configured with --with-arch=<isa>
set +e
make
if [ $? -eq 0 ] ; then
    make install
    RISCV_TEST_FAILED=0
else
    RISCV_TEST_FAILED=1
fi
set -e

# Build riscv-fesvr
echo "Building riscv-fesvr..."
cd $RISCV
mkdir build-fesvr
cd build-fesvr
../../riscv-fesvr/configure --prefix=$RISCV
make
make install

# Build riscv-isa-sim
echo "Building riscv-isa-sim..."
cd $RISCV
mkdir build-isa-sim
cd build-isa-sim
../../riscv-isa-sim/configure --prefix=$RISCV --with-fesvr=$RISCV
make
make install

cd $STARTINGDIR

if [ $RISCV_TEST_FAILED -eq 1 ] ; then
    echo ""
    echo "[WARNING] $ISA toolchain compiled successfully, but riscv-tests compilation failed."
    echo "If you need riscv-tests, try compiling them with a RV64G toolchain using ./build.sh"
else
    echo ""
    echo "$ISA toolchain and riscv-tests compiled successfully."
fi
