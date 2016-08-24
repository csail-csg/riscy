
// Copyright (c) 2016 Massachusetts Institute of Technology

// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation
// files (the "Software"), to deal in the Software without
// restriction, including without limitation the rights to use, copy,
// modify, merge, publish, distribute, sublicense, and/or sell copies
// of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

/*
 * This file is the configuration file for Riscy processors. This file defines
 * macros that are used during the BSV compilation process to select what
 * processor to build.
 *
 * This ProcConfig.bsv is for connectal-based designs. When a connectal flag
 * is added to the makefile like so:
 *   CONNECTALFLAGS += -D FOO=5
 * The flag FOO is defined to be 5 throughout the build process (Makefile,
 * BSV, C++, and TCL). The makefile for each connectal-based processor has
 * defined macros to give information about the processor to build.
 *
 * If you want to make a non-connectal-based design, then you will implement
 * your own ProcConfig.bsv where you define only the BSV macros you want in
 * your design.
 */

// BSV Macros derived from project defined macros. Project defined macros are
// defined in connectal Makefiles
`include "ConnectalProjectConfig.bsv"
// verilator/generatedbsv/ConnectalProjectConfig.bsv

// ISA size
`ifdef CONFIG_RV64
    `define rv64
`endif

`ifdef CONFIG_RV32
    `define rv32
`endif

// privilege levels
`ifdef CONFIG_S
    `define s
`endif

`ifdef CONFIG_U
    `define u
`endif

// ISA extensions
`ifdef CONFIG_M
    `define m
`endif

`ifdef CONFIG_A
    `define a
`endif

`ifdef CONFIG_F
    `define f
`endif

`ifdef CONFIG_D
    `define d
`endif

// BSV-only macros
`define REUSE_FMA
// `define NO_FDIV
// `define NO_FSQRT
// `define USE_DUMMY_FPU

// Debugging infrastructure
`define VERIFICATION_PACKETS

// Workarounds

