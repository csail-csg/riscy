
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

#include <assert.h>
#include "spike/encoding.h" // I would include fesvr's encoding.h here but it isn't installed

// ConnectalProjectConfig.h contains CONFIG_* macro definitions.
#include "ConnectalProjectConfig.h"

#include "HTIF.hpp"

HTIF::HTIF(const std::vector<std::string>& args, ProcControl *procControlIn, Platform *platformIn)
    : htif_t(args),
      procControl(procControlIn),
      platform(platformIn),
      verbose(false) {
    // XXX: Do we need to do anything to construct HTIF?
    // no?
}

HTIF::~HTIF() {
    // XXX: Do we need to do anything to destruct HTIF?
    // no?
}

void HTIF::start() {
    if (verbose) fprintf(stderr, "HTIF::start() called\n");
    // htif_t::start reads the config string to get the number of cores also,
    // but we don't always have a config string, so that's not necessary
    load_program();
    reset();
#ifdef CONFIG_START_PC_0
    procControl->start(0);
#else
    procControl->start(0x1000);
#endif
}

void HTIF::stop() {
    if (verbose) fprintf(stderr, "HTIF::stop() called\n");
    // don't really need to do anyhting else
    procControl->stop();
    htif_t::stop();
}

void HTIF::read_chunk(addr_t taddr, size_t len, void* dst)
{
    platform->read_chunk(taddr, len, dst);
}

void HTIF::write_chunk(addr_t taddr, size_t len, const void* src)
{
    platform->write_chunk(taddr, len, src);
}

void HTIF::load_program() {
    if (verbose) fprintf(stderr, "HTIF::load_program() called\n");
    // don't really need to do anyhting else
    htif_t::load_program();
}

void HTIF::reset()
{
    if (verbose) fprintf(stderr, "HTIF::reset() called\n");
    procControl->reset();
}

