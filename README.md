Riscy Processors - Open-Sourced RISC-V Processors 
=================================================

This repository contains a collection of open-sourced RISC-V processors written in Bluespec System Verilog (BSV).

These processors can be built with a variety of backends to use the processors in different simulation frameworks or FPGA.
Currently the supported backends are Connectal and Verilator.
Connectal is a generic framework that supports a variety of FPGAs and simulation targets.

## Getting Started

How to get started with this repository (tested in Ubuntu 14.04):

1. Get all the submodules.

        $ git submodule update --init --recursive

2. Get dependencies for building the RISC-V toolchain and building using connectal.

        $ sudo apt-get install autoconf automake autotools-dev curl libmpc-dev libmpfr-dev libgmp-dev gawk build-essential bison flex texinfo gperf libtool patchutils bc python-ply

3. Build riscv-gnu-toolchain and riscv-tests.
`build.sh` can be used to build custom toolchains by passing the desired RISC-V ISA string in all caps (eg: `./build.sh RV32IMC").
By default, `build.sh` builds the toolchain `tools/RV64G`.

        $ cd tools
        $ ./build.sh
        $ cd ..

4. Setup environment variables for the Riscy project.
You should either use this script from the top-level directory of the Riscy repository, or you should change the variable `RISCY_HOME` in the script to be the path to the Riscy repository.

        $ source ./setup.sh

5. Get a newer version of Verilator.
The version of Verilator in the Ubuntu package has a bug that prevents running our BSV designs.
We use a PPA to provide a newer version of Verilator.

        $ sudo apt-add-repository -y ppa:jamey-hicks/connectal
        $ sudo apt-get update
        $ sudo apt-get install verilator

7. Build the multicycle processor using the connectal backend with its verilator target.

        $ cd procs/RV64G_multicycle
        $ make build.verilator

8. Simulate tests by running `./runtests.sh` and then select the `connectal (verilator)` backend and which tests to run

