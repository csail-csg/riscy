
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

#ifndef HTIF_HPP
#define HTIF_HPP

#include "fesvr/htif.h"
#include "ProcControl.hpp"

class HTIF : public htif_t {
    public:
        HTIF(const std::vector<std::string>& args,
                uint64_t *rambuffIn,
                size_t ramszIn,
                uint64_t *rombuffIn,
                size_t romszIn,
                ProcControl *procControlIn);
        ~HTIF();

        // XXX: This is the main way things are run:
        // int run();
        // bool done();
        // int exit_code();

        // these can be redefined, but they don't need to be
        virtual void start(); // performs load_program() and reset()
        virtual void stop();

    private:
        void read_chunk(addr_t taddr, size_t len, void* dst);
        void write_chunk(addr_t taddr, size_t len, const void* src);

        size_t chunk_align() { return sizeof(uint64_t); }
        size_t chunk_max_size() { return (sizeof(uint64_t) * 1024); }

        virtual void load_program();
        virtual void reset();

        uint64_t *ramBuffer;
        size_t ramSz;
        uint64_t ramBaseAddr = 0x80000000; // XXX: Hardcoded for now
        uint64_t *romBuffer;
        size_t romSz;
        uint64_t romBaseAddr = 0x00000000; // XXX: Hardcoded for now

        ProcControl *procControl;

        bool verbose;
};

#endif
