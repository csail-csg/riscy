Riscy Processors - Open-Sourced RISC-V Processors 
=================================================

How to use (in Ubuntu 14.04):

1. Get all the submodules

        $ git submodule update --init --recursive

2. Edit setup.sh so `RISCY_HOME` points to the riscy directory
3. Setup environment for RISCY

        $ source ./setup.sh RV64IMAFD

4. Get dependencies for building riscv tools.

        $ sudo apt-get install autoconf automake autotools-dev curl libmpc-dev libmpfr-dev libgmp-dev gawk build-essential bison flex texinfo gperf libtool patchutils bc

5. Get newer version of Verilator. The version of Verilator in the Ubuntu package has a bug that prevents running our BSV designs. We use a PPA to provide a newer version of Verilator.

        $ sudo apt-add-repository -y ppa:jamey-hicks/connectal
        $ sudo apt-get update
        $ sudo apt-get install verilator

6. Build riscv-gnu-toolchain and riscv-tests

        $ cd tools
        $ ./build.sh RV64IMAFD

7. Build multicycle processor

        $ cd ../procs/RV64G_multicycle
        $ make build.verilator

8. Simulate tests by running `./runtests.sh` and then select which tests to run

