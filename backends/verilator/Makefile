
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

# PROC should be defined in another makefile
ifndef PROC
$(error PROC is not set)
endif

ifndef RISCY_HOME
$(error RISCY_HOME is not set)
endif

VERILATOR_EXE=$(PROC).exe

TOP_MODULE=mkProcVerilator
TOP_BSV_FILE=$(RISCY_HOME)/backends/verilator/bsv/ProcVerilator.bsv

# Build Directories
BUILD_DIR=build
BSC_DIR=$(BUILD_DIR)/bsc
VERILOG_DIR=$(BUILD_DIR)/verilog
VERILATOR_DIR=$(BUILD_DIR)/verilator



BSV_PATH = $(RISCY_HOME)/procs/riscy-lib:$(RISCY_HOME)/procs/$(PROC):$(RISCY_HOME)/backends/verilator/bsv:$(RISCY_HOME)/recycle-bsv-lib/src/bsv:+
BSC_DEFINES += -D CONFIG_IDMEM_INIT_HEX_FILE=\"idmem.hex\"
BSC_DEFINES += -D CONFIG_RAM_INIT_HEX_FILE=\"ram.hex\"
BSC_FLAGS = -aggressive-conditions -keep-fires $(BSC_DEFINES) -p $(BSV_PATH) -bdir $(BSC_DIR) -fdir $(BSC_DIR) -info-dir $(BSC_DIR) -simdir $(BSC_DIR) -vdir $(VERILOG_DIR)

VERILOG_PATH = -y $(BLUESPECDIR)/Verilog -y $(VERILOG_DIR)
VERILATOR_FLAGS = -Mdir $(VERILATOR_DIR) -CFLAGS -O2 $(VERILOG_PATH) -Wno-fatal --trace
VERILATOR_CPP = $(RISCY_HOME)/backends/verilator/cpp/verilator_top.cpp

.PHONY: verilator verilog clean

verilator: $(VERILATOR_EXE)

verilog: $(TOP_BSV_FILE) $(this)
	mkdir -p $(BSC_DIR)
	mkdir -p $(VERILOG_DIR)
	bsc $(BSC_FLAGS) -u -verilog -g $(TOP_MODULE) $(TOP_BSV_FILE)

$(VERILATOR_EXE): verilog
	mkdir -p $(VERILATOR_DIR)
	verilator --cc $(VERILATOR_FLAGS) -o $(VERILATOR_EXE) $(VERILOG_DIR)/$(TOP_MODULE).v --exe $(VERILATOR_CPP)
	make -C $(VERILATOR_DIR) -f V$(TOP_MODULE).mk
	cp $(VERILATOR_DIR)/$(VERILATOR_EXE) .

clean:
	rm -rf $(BSC_DIR) $(VERILOG_DIR) $(VERILATOR_DIR)
	rmdir --ignore-fail-on-non-empty $(BUILD_DIR)
	rm -rf $(VERILATOR_EXE)
