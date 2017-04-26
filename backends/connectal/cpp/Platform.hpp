
// Copyright (c) 2016, 2017 Massachusetts Institute of Technology

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

#include "DmaBuffer.h"
#include "PlatformIndication.h"
#include "PlatformRequest.h"
#include "GeneratedTypes.h"

class Platform : PlatformIndicationWrapper {
    public:
        Platform(unsigned int indicationId, unsigned int requestId, size_t ramBaseAddrIn, size_t ramSzIn);
        virtual ~Platform() {}

        virtual void init();

        bool load_elf(const char* elf_filename);

        // Functions to access the RISC-V's memory
        // These either access the memory through shared memory or through
        // the external memory interface.
        virtual void read_chunk(uint64_t taddr, size_t len, void* dst);
        virtual void write_chunk(uint64_t taddr, size_t len, const void* src);

    private:
        // Access the RISC-V's memory through the external memory interface
        uint64_t memRead(uint64_t addr);
        void memWrite(uint64_t addr, uint64_t data);
        void read_chunk_extIfc(uint64_t taddr, size_t len, void* dst);
        void write_chunk_extIfc(uint64_t taddr, size_t len, const void* src);

        // Read from shared memory
        void read_chunk_sharedMem(uint64_t taddr, size_t len, void* dst);
        void write_chunk_sharedMem(uint64_t taddr, size_t len, const void* src);

        // called by connectal thread
        void memResponse(const int write, const uint64_t data);

        template <typename Elf_Ehdr, typename Elf_Phdr>
        bool load_elf_specific(char* buf, size_t buf_sz);

        bool verbose;

        size_t ramBaseAddr;
        size_t ramSz;
        DmaBuffer ram;

        uint64_t* ramBuffer;

        PlatformRequestProxy *platformRequest;

        // used by both threads
        sem_t responseSem;
        uint64_t responseData;
};

#endif
