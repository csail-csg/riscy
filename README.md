riscy
=====

How to use:

1. `git submodule update --init --recursive`

2. Edit setup.sh so RISCY_HOME points to the riscy directory

3. `source ./setup.sh`

4. `cd riscv-tools`

5. ` sudo apt-get install autoconf automake autotools-dev curl libmpc-dev libmpfr-dev libgmp-dev gawk build-essential bison flex texinfo gperf libtool patchutils bc`

6. `./build.sh`

7. `cd ../procs/RV64G_multicycle`

8. `make build.verilator`

9. `./runtests.sh`

10. select which tests you want to run
