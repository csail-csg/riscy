
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

#include <errno.h>
#include <stdio.h>
#include <cstring>
#include <cassert>
#include <fcntl.h>
#include <string.h>
#include <iostream>
#include <sys/stat.h>
#include <unistd.h>
#include <semaphore.h>
#include <vector>
#include <string>
#include <sstream>
#include <list>
#include <signal.h>
#include "DmaBuffer.h"

#include "ProcControl.hpp"
#include "Verification.hpp"
#include "PerfMonitor.hpp"
#include "ExternalMMIO.hpp"
#include "HTIF.hpp"
#include "DeviceTree.hpp"

#include "NullTandemVerifier.hpp"
#include "SpikeTandemVerifier.hpp"

#include "GeneratedTypes.h"

#ifdef NDEBUG
#error fesvr will not work with NDEBUG defined
#endif

#define CONNECTAL_MEMORY

#define BLURT fprintf (stderr, "CPPDEBUG: %s(%s):%d\n",\
                      __func__, __FILE__, __LINE__)

// main stuff
static ProcControl *procControl = NULL;
static Verification *verification = NULL;
static PerfMonitor *perfMonitor = NULL;
static ExternalMMIO *externalMMIO = NULL;
static HTIF *htif = NULL;

// The amount of RAM attached to the processor. 64 MB by default
size_t ramSz = 64 * 1024 * 1024;
// The size of the ROM attached to the uncached region. 64 KB by default
size_t romSz = 64 * 1024;

// What do we do with this?
static void handle_signal(int sig) {
    fprintf(stderr, "\n>> Ctrl-C: Exiting...\n");
    if (verification != NULL) {
        verification->printStatus();
    }
    exit(1);
}

void printHelp(const char *prog)
{
    fprintf(stderr, "Usage: %s [--just-run] HTIF_ARGS\n", prog);
}

int main(int argc, char * const *argv) {
    // command line argument parsing
    // strip prog_name off of the command line arguments
    const char *prog_name = argv[0];
    argc--;
    argv++;
    // if the first argument is "-h" or "--help", print help
    if (argc > 0 && ((strcmp(argv[0], "-h") == 0) || (strcmp(argv[0], "--help") == 0))) {
        printHelp(prog_name);
        exit(0);
    }
    // if the next argument is "--just-run" remove it and set just_run to true
    bool just_run = false;
    bool just_trace = false;
    if (argc > 0 && strcmp(argv[0], "--just-run") == 0) {
        just_run = true;
        argc--;
        argv++;
    }
    if (argc > 0 && strcmp(argv[0], "--just-trace") == 0) {
        just_trace = true;
        argc--;
        argv++;
    }

    signal(SIGINT, &handle_signal);

    long actualFrequency = 0;
    long requestedFrequency = 1e9 / MainClockPeriod;

#ifdef SIMULATION // safe to always do this, but it's only useful for simulation
    char socket_name[128];
    snprintf(socket_name, sizeof(socket_name), "SOCK.%d", getpid());
    setenv("BLUESIM_SOCKET_NAME", socket_name, 0);
    setenv("SOFTWARE_SOCKET_NAME", socket_name, 0);
#endif

    // format htif args
    std::vector<std::string> htif_args;
    fprintf(stderr, "htif_args: ");
    for (int i = 0 ; i < argc ; i++ ) {
        // adding argument
        htif_args.push_back(argv[i]);
        // printing arguments
        fprintf(stderr, "%s", argv[i]);
        if (i == argc-1) {
            fprintf(stderr, "\n");
        } else {
            fprintf(stderr, ", ");
        }
    }

    // objects for controlling the interaction with the processor
    procControl = new ProcControl(IfcNames_ProcControlIndicationH2S, IfcNames_ProcControlRequestS2H);
    if (just_run) {
        procControl->configureVerificationPackets(0xFFFFFFFFFFFFFFFFLL, false);
        verification = new Verification(IfcNames_VerificationIndicationH2S, new NullTandemVerifier());
    } else if (just_trace) {
        verification = new Verification(IfcNames_VerificationIndicationH2S, new NullTandemVerifier());
    } else {
        // ERROR
        fprintf(stderr, "WARNING: Spike-based tandem verification is not fully tested for priv spec v1.9 yet\n");
        verification = new Verification(IfcNames_VerificationIndicationH2S, new SpikeTandemVerifier(htif_args, ramSz));
    }
    perfMonitor = new PerfMonitor(IfcNames_PerfMonitorIndicationH2S, IfcNames_PerfMonitorRequestS2H);
    externalMMIO = new ExternalMMIO(IfcNames_ExternalMMIORequestH2S, IfcNames_ExternalMMIOResponseS2H);

    int status = setClockFrequency(0, requestedFrequency, &actualFrequency);
    printf("Requested main clock frequency %5.2f, actual clock frequency %5.2f MHz status=%d errno=%d\n",
        (double)requestedFrequency * 1.0e-6,
        (double)actualFrequency * 1.0e-6,
        status, (status != 0) ? errno : 0);

    // initialize dram and rom
    DmaBuffer ram(ramSz, false); // false == uncached
    DmaBuffer rom(romSz, false); // false == uncached
    procControl->configure(ram.reference(),
                           ramSz,
                           rom.reference(),
                           romSz);

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
    memcpy( (void*) &((char*) rom.buffer())[0x1000], (void*) reset_vec, 8 * sizeof(uint32_t) );
    memcpy( (void*) &((char*) rom.buffer())[0x1020], (void*) s.str().c_str(), s.str().size() );

    // Connect an HTIF module up to the procControl interfaces
    htif = new HTIF(htif_args, (uint64_t*) ram.buffer(), ramSz, (uint64_t*) rom.buffer(), romSz, procControl);

    // This function loads the specified program, and runs the test
    int result = htif->run();
    perfMonitor->setEnable(0);

    if (result == 0) {
        fprintf(stderr, "[32mPASSED[39m\n");
    } else {
        fprintf(stderr, "[31mFAILED %d[39m\n", (int) result);
    }

#ifdef SIMULATION
    unlink(socket_name);
#endif

    fprintf(stderr, "---- Verification results: ------------------------------------------\n");
    verification->printStatus();
    fprintf(stderr, "\n");
    fprintf(stderr, "---- PerfMonitor results: -------------------------------------------\n");
    perfMonitor->printPerformance("verilator/Proc.perfmon.txt");
    fprintf(stderr, "\n");

    fflush(stdout);
    fflush(stderr);

    return result;
}
