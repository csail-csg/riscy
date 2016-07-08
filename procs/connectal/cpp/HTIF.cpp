
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
#include "HTIF.hpp"

HTIF::HTIF(const std::vector<std::string>& args, uint64_t *memBufferIn, size_t memSzIn , ProcControl *procControlIn, HostInterface *hostInterfaceIn) :
        htif_t(args), memBuffer(memBufferIn), memSz(memSzIn), procControl(procControlIn), hostInterface(hostInterfaceIn), verbose(false) {
    // XXX: Do we need to do anything to construct HTIF?
    // no?
}

HTIF::~HTIF() {
    // XXX: Do we need to do anything to destruct HTIF?
    // no?
}

void HTIF::start() {
    if (verbose) fprintf(stderr, "HTIF::start() called\n");
    // don't really need to do anyhting else
    htif_t::start();
    // assert(!started);
    // started = true;
    // if (!targs.empty() && targs[0] != "none")
    //     load_program();
    // reset();
}

void HTIF::stop() {
    if (verbose) fprintf(stderr, "HTIF::stop() called\n");
    // don't really need to do anyhting else
    htif_t::stop();
    // if (!sig_file.empty() && sig_len) { // print final torture test signature
    //     std::vector<uint8_t> buf(sig_len);
    //     mem.read(sig_addr, sig_len, &buf[0]);
    //     std::ofstream sigs(sig_file);
    //     assert(sigs && "can't open signature file!");
    //     sigs << std::setfill('0') << std::hex;
    //     const addr_t incr = 16;
    //     assert(sig_len % incr == 0);
    //     for (addr_t i = 0; i < sig_len; i += incr) {
    //         for (addr_t j = incr; j > 0; j--) {
    //             sigs << std::setw(2) << (uint16_t)buf[i+j-1];
    //         }
    //         sigs << '\n';
    //     }
    //     sigs.close();
    // }
    // for (uint32_t i = 0, nc = num_cores(); i < nc; i++) {
    //     write_cr(i, CSR_MRESET, 1);
    // }
    // stopped = true;
}

reg_t HTIF::read_cr(uint32_t coreid, uint16_t regnum) {
    reg_t regno = (reg_t) regnum;
    uint64_t val = 0;

    // system control register space
    if ((coreid & 0xFFFFF) == 0xFFFFF) {
        switch (regnum) {
            case 0:     return 1; // number of procs
            case 1:     return memSz >> 20; // size of memory in MB
            default:    return 0; // this is an unsupported CSR
        }
    } else {
        switch (regno) {
            case CSR_MTOHOST:
                // Read mtohost
                // This function returns true if there was a new message, but
                // we aren't using that information right now. Not sure what
                // we can do with it.
                hostInterface->getToHostMessage(&val);
                return val;
            case CSR_MFROMHOST:
                if (verbose) fprintf(stderr, "%s:%d Reading mfromhost CSR is unsupported\n", __FILE__, __LINE__);
                return 0;
            case CSR_MRESET:
                fprintf(stderr, "%s:%d Reading mreset CSR is unsupported\n", __FILE__, __LINE__);
                return 0;
            default:
                fprintf(stderr, "%s:%d Reading unknown CSR\n", __FILE__, __LINE__);
                return 0;
        }
    }
    fprintf(stderr, "%s:%d Can't find CSR to read\n", __FILE__, __LINE__);
    return 0;
}

reg_t HTIF::write_cr(uint32_t coreid, uint16_t regnum, reg_t val) {
    reg_t regno = (reg_t) regnum;

    // system control register space
    if ((coreid & 0xFFFFF) == 0xFFFFF) {
        fprintf(stderr, "%s:%d Trying to write to read-only system control register space\n", __FILE__, __LINE__);
        switch (regnum) {
            case 0:     return 1; // number of procs
            case 1:     return memSz >> 20; // size of memory in MB
            default:    return 0; // this is an unsupported CSR
        }
    } else {
        switch (regno) {
            case CSR_MTOHOST:
                if (val != 0) {
                    fprintf(stderr, "%s:%d Writing non-zero values to mtohost CSR is unsupported\n", __FILE__, __LINE__);
                }
                reg_t ret;
                hostInterface->getToHostMessage(&ret);
                return ret;
            case CSR_MFROMHOST:
                hostInterface->putFromHostMessage(val);
                return 0;
            case CSR_MRESET:
                // This emulates an mreset CSR by calling stop when 1 is
                // written to the CSR and calling reset and start when 0 is
                // written.
                if (val == 1) {
                    if (verbose) fprintf(stderr, "HTIF::write_cr() - writing 1 to mreset CSR -> stopping\n");
                    // stop
                    procControl->stop();
                } else if (val == 0) {
                    if (verbose) fprintf(stderr, "HTIF::write_cr() - writing 0 to mreset CSR -> resetting and starting\n");
                    // reset
                    procControl->reset();
                    procControl->start(0x200);
                }
                return 0;
            default:
                fprintf(stderr, "%s:%d Writing to unknown CSR\n", __FILE__, __LINE__);
                return 0;
        }
    }
    fprintf(stderr, "%s:%d Can't find CSR to write\n", __FILE__, __LINE__);
    return 0;
}

void HTIF::read_chunk(addr_t taddr, size_t len, void* dst)
{
    assert(memBuffer != NULL);
    assert(taddr >= 0);
    assert(taddr + len <= memSz);

    if (verbose) fprintf(stderr, "HTIF::read_chunk(taddr=0x%lx, len=%ld, dst=%p)\n", (long)taddr, (long)len, dst);

    memcpy(dst, &memBuffer[taddr/sizeof(uint64_t)], len);
}

void HTIF::write_chunk(addr_t taddr, size_t len, const void* src)
{
    assert(memBuffer != NULL);
    assert(taddr >= 0);
    assert(taddr + len <= memSz);

    if (verbose) fprintf(stderr, "HTIF::write_chunk(taddr=0x%lx, len=%ld, src=%p)\n", (long)taddr, (long)len, src);

    memcpy(&memBuffer[taddr/sizeof(uint64_t)], src, len);
}

void HTIF::load_program() {
    if (verbose) fprintf(stderr, "HTIF::load_program() called\n");
    // don't really need to do anyhting else
    htif_t::load_program();
    // std::string path;
    // if (access(targs[0].c_str(), F_OK) == 0)
    //   path = targs[0];
    // else if (targs[0].find('/') == std::string::npos)
    // {
    //   std::string test_path = PREFIX TARGET_DIR + targs[0];
    //   if (access(test_path.c_str(), F_OK) == 0)
    //     path = test_path;
    // }

    // if (path.empty())
    //   throw std::runtime_error("could not open " + targs[0]);

    // std::map<std::string, uint64_t> symbols = load_elf(path.c_str(), &mem);

    // // detect torture tests so we can print the memory signature at the end
    // if (symbols.count("begin_signature") && symbols.count("end_signature"))
    // {
    //   sig_addr = symbols["begin_signature"];
    //   sig_len = symbols["end_signature"] - sig_addr;
    // }
}

// htif_t::reset() writes 1 then 0 to each core
void HTIF::reset()
{
    if (verbose) fprintf(stderr, "HTIF::reset() called\n");
    // for now, lets just use the original function
    htif_t::reset();
}

///////////////////////////////////////
// 
// int htif_t::run()
// {
//   start();
//   std::vector<std::queue<reg_t>> fromhost(num_cores());
// 
//   auto enq_func = [](std::queue<reg_t>* q, uint64_t x) { q->push(x); };
//   std::vector<std::function<void(reg_t)>> fromhost_callbacks;
//   for (size_t i = 0; i < num_cores(); i++)
//     fromhost_callbacks.push_back(std::bind(enq_func, &fromhost[i], std::placeholders::_1));
// 
//   while (!signal_exit && exitcode == 0)
//   {
//     for (uint32_t coreid = 0; coreid < num_cores(); coreid++)
//     {
//       if (auto tohost = write_cr(coreid, CSR_MTOHOST, 0))
//       {
//         command_t cmd(this, tohost, fromhost_callbacks[coreid]);
//         device_list.handle_command(cmd);
//       }
// 
//       device_list.tick();
// 
//       if (!fromhost[coreid].empty())
//         if (write_cr(coreid, CSR_MFROMHOST, fromhost[coreid].front()) == 0)
//           fromhost[coreid].pop();
//     }
//   }
// 
//   stop();
// 
//   return exit_code();
// }
