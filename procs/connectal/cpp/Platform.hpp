
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

#ifndef PLATFORM_HPP
#define PLATFORM_HPP

#include "fesvr/memif.h"

#include "DmaBuffer.h"
#include "PlatformIndication.h"
#include "PlatformRequest.h"
#include "GeneratedTypes.h"

class Platform : PlatformIndicationWrapper {
    public:
        Platform(unsigned int indicationId, unsigned int requestId, size_t ramBaseAddrIn, size_t ramSzIn, size_t romBaseAddrIn, size_t romSzIn);
        virtual ~Platform() {}

        virtual void init();

        uint64_t memRead(uint64_t addr);
        void memWrite(uint64_t addr, uint64_t data);

        // functions for accessing the platform
        virtual void read_chunk(addr_t taddr, size_t len, void* dst);
        virtual void write_chunk(addr_t taddr, size_t len, const void* src);
        virtual size_t chunk_align();
        virtual size_t chunk_max_size();

    private:
        // called by connectal thread
        void memResponse(const int write, const uint64_t data);

        bool verbose;

        size_t ramBaseAddr;
        size_t ramSz;
        DmaBuffer ram;

        size_t romBaseAddr;
        size_t romSz;
        DmaBuffer rom;

        uint64_t* ramBuffer;
        uint64_t* romBuffer;

        PlatformRequestProxy *platformRequest;

        // used by both threads
        sem_t responseSem;
        uint64_t responseData;
};

#endif
