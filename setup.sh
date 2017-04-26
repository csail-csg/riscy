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

# This script takes an optional argument for toolchains built for specific
# subsets of the RISC-V ISA.

# Points to root folder of repository
export RISCY_HOME=$PWD

[ "$0" == "$BASH_SOURCE" ] && echo "[WARNING] This scipt needs to be sourced to correctly setup the environment variables"

if [ ! -d $RISCY_HOME/tools ] ; then
    echo "[ERROR] Can't find folder $RISCY_HOME/tools"
    echo ""
    echo "Either this script needs to be run at the top level of the Riscy"
    echo "repo, or you need to set RISCY_HOME to be the path to the Riscy"
    echo "repo inside this script"
    return 1
fi

if [ $# -eq 0 ] ; then
    TOOLCHAIN=RV64G
else
    TOOLCHAIN=$1
fi

# TOOLCHAIN should be an ISA string like RV32IM

if echo "$TOOLCHAIN" | grep -vqE "^RV(32|64)" ; then
    # error
    echo "[ERROR] This script expects a RISC-V ISA string in all caps as the"
    echo "command line argument (example: RV64IMAFDC)"
    return 1
fi

if [ ! -d $RISCY_HOME/tools/$TOOLCHAIN ] ; then
    if [ "$TOOLCHAIN" == "RV64G" ] ; then
        BUILD_COMMAND="./build.sh"
    else
        BUILD_COMMAND="./build.sh $TOOLCHAIN"
    fi

    echo "[WARNING] $RISCY_HOME/tools/$TOOLCHAIN does not exist"
    echo ""
    echo "To use this toolchain you need to build it first by going to the tools folder and running $BUILD_COMMAND"
    # echo ""
    # read -p "Would you like to start building the toolchain now? [N/y] " RESP
    # case $RESP in
    #     [Yy]*) pushd $RISCY_HOME/tools ; $BUILD_COMMAND ; popd ;;
    # esac
fi

# Points to toolchain
export RISCY_TOOLS=$RISCY_HOME/tools/$TOOLCHAIN
# Adding to path and ld library path
export PATH=$RISCY_TOOLS/bin:$PATH
if [ "$LD_LIBRARY_PATH" == "" ] ; then
    export LD_LIBRARY_PATH=$RISCY_TOOLS/lib
else
    export LD_LIBRARY_PATH=$RISCY_TOOLS/lib:$LD_LIBRARY_PATH
fi
