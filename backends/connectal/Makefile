
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

# PROC should be defined in another makefile
ifndef PROC
$(error PROC is not set)
endif

ifndef RISCY_HOME
$(error RISCY_HOME is not set)
endif

CONNECTALDIR ?= $(RISCY_HOME)/connectal

# Add accelerators if ACCELERATORS was defined
ifdef ACCELERATORS
CONNECTALFLAGS += -D CONFIG_ACCELERATOR

include $(RISCY_HOME)/accelerators/Makefile.accelerators

BSVFILES += $(ACCEL_BSVFILES)
BSVPATH += $(ACCEL_BSVPATH)

BSVFILES += $(RISCY_HOME)/procs/$(PROC)/accelerator/generatedbsv/AccelTop.bsv
BSVPATH += $(RISCY_HOME)/procs/$(PROC)/accelerator/generatedbsv
endif

BSVPATH += \
	$(RISCY_HOME)/procs/riscy-lib \
	$(RISCY_HOME)/procs/$(PROC) \
	$(RISCY_HOME)/backends/connectal/bsv \
	$(RISCY_HOME)/recycle-bsv-lib/src/bsv \

BSVFILES += \
	$(RISCY_HOME)/procs/riscy-lib/ProcPins.bsv \
	$(RISCY_HOME)/procs/riscy-lib/VerificationPacket.bsv \
	$(RISCY_HOME)/backends/connectal/bsv/ProcConnectal.bsv \
	$(RISCY_HOME)/recycle-bsv-lib/src/bsv/PerfMonitorConnectal.bsv \

CPPFILES += \
	$(RISCY_HOME)/backends/connectal/cpp/testproc.cpp \
	$(RISCY_HOME)/backends/connectal/cpp/Platform.cpp \
	$(RISCY_HOME)/backends/connectal/cpp/ProcControl.cpp \
	$(RISCY_HOME)/backends/connectal/cpp/Verification.cpp \
	$(RISCY_HOME)/backends/connectal/cpp/ExternalMMIO.cpp \
	$(RISCY_HOME)/backends/connectal/cpp/SpikeTandemVerifier.cpp \
	$(RISCY_HOME)/backends/connectal/cpp/PrintTrace.cpp \
	$(RISCY_HOME)/backends/connectal/cpp/ElfLoader.cpp \
	$(RISCY_HOME)/backends/connectal/cpp/UartBridge.cpp \
	$(RISCY_HOME)/recycle-bsv-lib/src/cpp/PerfMonitor.cpp \
	$(CONNECTALDIR)/cpp/DmaBuffer.cpp \

S2H_INTERFACES = \
	ProcControlRequest:ProcConnectal.procControlRequest \
	PerfMonitorRequest:ProcConnectal.perfMonitorRequest \
	PlatformRequest:ProcConnectal.platformRequest \
	UartBridgeRequest:ProcConnectal.uartBridgeRequest \
	ExternalMMIOResponse:ProcConnectal.externalMMIOResponse \

H2S_INTERFACES = \
	ProcConnectal:ProcControlIndication \
	ProcConnectal:PlatformIndication \
	ProcConnectal:VerificationIndication \
	ProcConnectal:PerfMonitorIndication \
	ProcConnectal:UartBridgeIndication \
	ProcConnectal:ExternalMMIORequest \

MEM_READ_INTERFACES = \
	lProcConnectal.dmaReadClient \

MEM_WRITE_INTERFACES = \
	lProcConnectal.dmaWriteClient \

NUMBER_OF_MASTERS = 1

PINOUT_FILE += $(RISCY_HOME)/backends/connectal/pin_translation.json
PIN_TYPE = ProcPins
PIN_TYPE_INCLUDE = ProcPins
AUTOTOP = --interface pins:ProcConnectal.pins

# Expand the stack used by BSC
CONNECTALFLAGS += --bscflags="+RTS -K250000000 -RTS"
# Don't use buildcache
CONNECTALFLAGS += --nocache
# Use a 32ns clock period
CONNECTALFLAGS += --mainclockperiod=32
# Don't add extra latency to simulation DMA accesses
CONNECTALFLAGS += -D SIM_DMA_READ_LATENCY=1 -D SIM_DMA_WRITE_LATENCY=1
# Use ACP (necessary for zc706)
CONNECTALFLAGS += -D USE_ACP
# Include locations for cpp
CONNECTALFLAGS += -I$(RISCY_HOME)/recycle-bsv-lib/src/cpp -I$(RISCY_TOOLS)/include

# Verilator defines: enable -jN for parallel c++ compilation and split the
# generated C++ into more source files
VERILATOR_DEFINES=VM_PARALLEL_BUILDS=1 VERILATOR_PROJECT_ARGS="-output-split 10000"

ifeq ($(BOARD),zc706)
ZYNQ=true
endif
ifeq ($(BOARD),zybo)
ZYNQ=true
endif
ifeq ($(BOARD),miniitx100)
ZYNQ=true
endif

ifneq ($(ZYNQ),true)

# For non-zync targets, use shared objects for spike and fesvr
CONNECTALFLAGS += --cxxflags=" -std=gnu++11" --clibdir=$(RISCY_TOOLS)/lib --clib=riscv --clib=fesvr

else

# For zync targets, use static linking for spike and fesvr
CONNECTALFLAGS += --cxxflags=" -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -D__STDC_CONSTANT_MACROS "
CONNECTALFLAGS += -I$(RISCY_HOME)/tools/riscv-isa-sim/riscv/insns
CONNECTALFLAGS += -I$(RISCY_HOME)/tools/riscv-isa-sim/riscv
CONNECTALFLAGS += -I$(RISCY_HOME)/tools/riscv-isa-sim/
CONNECTALFLAGS += -I$(RISCY_HOME)/tools/riscv-isa-sim/hwacha
CONNECTALFLAGS += -I$(RISCY_TOOLS)/include/spike
CONNECTALFLAGS += --stl=c++_static --cxxflags=" -UNDEBUG -std=gnu++11 -fexceptions "

FESVR_SRC_DIR = $(RISCY_HOME)/tools/riscv-fesvr/fesvr
FESVR_SRC_FILES = $(addprefix $(FESVR_SRC_DIR)/, context.cc htif.cc htif_pthread.cc device.cc memif.cc rfb.cc syscall.cc elfloader.cc term.cc)
SPIKE_SRC_DIR = $(RISCY_HOME)/tools/riscv-isa-sim
SPIKE_RISCV_SRC_FILES = \
	processor.cc \
	execute.cc \
	sim.cc \
	interactive.cc \
	trap.cc \
	cachesim.cc \
	mmu.cc \
	extension.cc \
	extensions.cc \
	rocc.cc \
	regnames.cc \
	devices.cc \
	rom.cc \
	rtc.cc \
	debug_module.cc \

SPIKE_SRC_FILES = $(addprefix $(SPIKE_SRC_DIR)/, spike_main/disasm.cc $(addprefix riscv/, $(SPIKE_RISCV_SRC_FILES))) \
	$(wildcard $(SPIKE_SRC_DIR)/softfloat/*.c) \
	$(wildcard $(SPIKE_SRC_DIR)/build/*.cc)
CPPFILES += $(FESVR_SRC_FILES) $(SPIKE_SRC_FILES)

endif

isatest.%: gen.%
	$(RISCY_HOME)/procs/scripts/isatest.sh $*/bin/ubuntu.exe

exe.%: gen.%
	$(MAKE) -C $* --no-print-directory exe

include $(CONNECTALDIR)/Makefile.connectal
