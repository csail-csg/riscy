
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

#include <iostream>
#include <sstream>

#include <assert.h>

#include "Platform.hpp"

Platform::Platform(unsigned int requestId, size_t ramBaseAddrIn, size_t ramSzIn, size_t romBaseAddrIn, size_t romSzIn)
        : verbose(false),
          ramBaseAddr(ramBaseAddrIn),
          ramSz(ramSzIn),
          ram(ramSzIn, false), // false == uncached
          romBaseAddr(romBaseAddrIn),
          romSz(romSzIn),
          rom(romSzIn, false) { // false == uncached
    // check if ram and rom overlap
    bool overlap = false;
    if (romBaseAddr < ramBaseAddr) {
        // rom < ram
        if (romBaseAddr + romSz > ramBaseAddr) {
            overlap = true;
        }
    } else {
        // ram <= rom
        if (ramBaseAddr + ramSz > romBaseAddr) {
            overlap = true;
        }
    }
    if (overlap) {
        std::cerr << "[WARNING] Platform::Platform : ROM and RAM regions overlap" << std::endl;
    }

    ramBuffer = (uint64_t*) ram.buffer();
    romBuffer = (uint64_t*) rom.buffer();

    platformRequest = new PlatformRequestProxy(requestId);

    platformRequest->configure(ram.reference(), ramSz, rom.reference(), romSz);
}

void Platform::init() {
    // Populate the ROM with the reset vector and config string
    // TODO: make number of processors a variable (currently 1)
    // TODO: make ISA string a variable
    // This matches the reset vec and config string from Spike's processor
    uint32_t reset_vec[8] = {
      0x297 + (0x80000000 - 0x1000),      // reset vector
      0x00028067,                         //   jump straight to DRAM_BASE
      0x00000000,                         // reserved
      0x00001020,                         // config string pointer
      0, 0, 0, 0                          // trap vector
    };
    std::stringstream s;
    s << std::hex <<
          "platform {\n"
          "  vendor ucb;\n"
          "  arch spike;\n"
          "};\n"
          "rtc {\n"
          "  addr 0x40000000;\n"
          "};\n"
          "ram {\n"
          "  0 {\n"
          "    addr 0x80000000;\n"
          "    size 0x" << ramSz << ";\n"
          "  };\n"
          "};\n"
          "core {\n"
          "  0 {\n"
          "    0 {\n"
          "      isa " << "rv64imafd" << ";\n"
          "      timecmp 0x40000008;\n"
          "      ipi 0x40001000;\n"
          "    };\n"
          "  };\n"
          "};\n";

    // XXX: What is the "correct" way to do this?
    memcpy( (void*) &((char*) romBuffer)[0x1000], (void*) reset_vec, 8 * sizeof(uint32_t) );
    memcpy( (void*) &((char*) romBuffer)[0x1020], (void*) s.str().c_str(), s.str().size() );
}

void Platform::read_chunk(addr_t taddr, size_t len, void* dst) {
    assert(romBuffer != NULL);
    assert(ramBuffer != NULL);
    assert(taddr >= 0);

    if ((taddr >= romBaseAddr) && (taddr + len <= romBaseAddr + romSz)) {
        // rom address
        if (verbose) fprintf(stderr, "Platform::read_chunk(taddr=0x%lx, len=%ld, dst=%p) from ROM address\n", (long)taddr, (long)len, dst);
        memcpy(dst, &romBuffer[(taddr - romBaseAddr)/sizeof(uint64_t)], len);
    } else if ((taddr >= ramBaseAddr) && (taddr + len <= ramBaseAddr + ramSz)) {
        // ram address
        if (verbose) fprintf(stderr, "Platform::read_chunk(taddr=0x%lx, len=%ld, dst=%p) from RAM address\n", (long)taddr, (long)len, dst);
        memcpy(dst, &ramBuffer[(taddr - ramBaseAddr)/sizeof(uint64_t)], len);
    } else {
        // illegal address
        if (verbose) fprintf(stderr, "[WARNING] Platform::read_chunk(taddr=0x%lx, len=%ld, dst=%p) from illegal address\n", (long)taddr, (long)len, dst);
    }
}

void Platform::write_chunk(addr_t taddr, size_t len, const void* src) {
    assert(romBuffer != NULL);
    assert(ramBuffer != NULL);
    assert(taddr >= 0);

    if ((taddr >= romBaseAddr) && (taddr + len <= romBaseAddr + romSz)) {
        // rom address
        if (verbose) fprintf(stderr, "Platform::write_chunk(taddr=0x%lx, len=%ld, src=%p) from ROM address\n", (long)taddr, (long)len, src);
        memcpy(&romBuffer[(taddr - romBaseAddr)/sizeof(uint64_t)], src, len);
    } else if ((taddr >= ramBaseAddr) && (taddr + len <= ramBaseAddr + ramSz)) {
        // ram address
        if (verbose) fprintf(stderr, "Platform::write_chunk(taddr=0x%lx, len=%ld, src=%p) from RAM address\n", (long)taddr, (long)len, src);
        memcpy(&ramBuffer[(taddr - ramBaseAddr)/sizeof(uint64_t)], src, len);
    } else {
        // illegal address
        if (verbose) fprintf(stderr, "[WARNING] Platform::write_chunk(taddr=0x%lx, len=%ld, src=%p) from illegal address\n", (long)taddr, (long)len, src);
    }
}

size_t Platform::chunk_align() {
    return sizeof(uint64_t);
}

size_t Platform::chunk_max_size() {
    return 1024 * sizeof(uint64_t);
}
