
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

`define rv64
// privilege levels
`define s
`define u
// ISA extensions
`define m
`define a
`define f
`define d

// Set this define to use the FMA for Add and Mul
`define REUSE_FMA
// `define NO_FDIV
// `define NO_FSQRT
// `define USE_DUMMY_FPU

// Defines to match spike's behavior
// `define CYCLE_COUNT_EQ_INST_COUNT
`define DISABLE_STIP
`define LOOK_LIKE_A_ROCKET

// Debugging infrastructure
`define VERIFICATION_PACKETS

// Workarounds
// `define WORKAROUND_ISSUE_27
// `define SERIALIZE_MEM_REQS
`define FLUSH_CACHES_ON_HTIF

