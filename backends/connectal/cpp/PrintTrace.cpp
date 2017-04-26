
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

#include <iomanip>
#include <iostream>
#include <sstream>
#include "spike/encoding.h"
#include "spike/mmu.h"
#include "spike/trap.h"

// ConnectalProjectConfig.h contains CONFIG_* macro definitions.
#include "ConnectalProjectConfig.h"

#include "PrintTrace.hpp"

PrintTrace::PrintTrace()
        : TandemVerifier(),
#ifdef CONFIG_RV64
          disassembler(new disassembler_t(64)),
#else
          disassembler(new disassembler_t(32)),
#endif
          packets(0),
          outBuffer(40) {
    pthread_mutex_init(&mutex, 0);
}

PrintTrace::~PrintTrace() {
    pthread_mutex_lock(&mutex);
    delete disassembler;
    pthread_mutex_destroy(&mutex);
}

bool PrintTrace::checkVerificationPacket(VerificationPacket packet) {
    pthread_mutex_lock(&mutex);

    bool match = true;
    
    outBuffer.addLine(verificationPacketToString(packet));

    // XXX: this was to temporarily print everything
    outBuffer.printToOStream(&std::cerr, 20000);

    pthread_mutex_unlock(&mutex);

    return match;
}

std::string PrintTrace::verificationPacketToString(VerificationPacket p) {
    std::ostringstream buffer;
    // pc
    buffer << "0x" << std::setfill('0') << std::setw(8) << std::hex << p.pc << ": ";
    // instruction data
    buffer << "(0x" << std::setfill('0') << std::setw(8) << std::hex << p.instruction << ") ";
    // instruction disassembled
    std::string assembly = (disassembler->disassemble(p.instruction));
    buffer << std::left << std::setfill(' ') << std::setw(32) << assembly;

    if (p.exception) {
        switch (p.cause) {
            case 0x00:
                buffer << " [Exception: Instruction address misaligned]";
                break;
            case 0x01:
                buffer << " [Exception: Instruction access fault]";
                break;
            case 0x02:
                buffer << " [Exception: Illegal instruction]";
                break;
            case 0x03:
                buffer << " [Exception: Breakpoint]";
                break;
            case 0x04:
                buffer << " [Exception: Load address misaligned]";
                break;
            case 0x05:
                buffer << " [Exception: Load access fault]";
                break;
            case 0x06:
                buffer << " [Exception: Store/AMO address misaligned]";
                break;
            case 0x07:
                buffer << " [Exception: Store/AMO access fault]";
                break;
            case 0x08:
                buffer << " [Exception: Environment call from U-mode]";
                break;
            case 0x09:
                buffer << " [Exception: Environment call from S-mode]";
                break;
            case 0x0A:
                buffer << " [Exception: Environment call from H-mode]";
                break;
            case 0x0B:
                buffer << " [Exception: Environment call from M-mode]";
                break;
            default:
                buffer << " [Unknown Exception]";
        }
    } else if (p.interrupt) {
        switch (p.cause) {
            case 0x00:
                buffer << " [Interrupt: User software interrupt]";
                break;
            case 0x01:
                buffer << " [Interrupt: Supervisor software interrupt]";
                break;
            case 0x02:
                buffer << " [Interrupt: Hypervisor software interrupt]";
                break;
            case 0x03:
                buffer << " [Interrupt: Machine software interrupt]";
                break;
            case 0x04:
                buffer << " [Interrupt: User timer interrupt]";
                break;
            case 0x05:
                buffer << " [Interrupt: Supervisor timer interrupt]";
                break;
            case 0x06:
                buffer << " [Interrupt: Hypervisor timer interrupt]";
                break;
            case 0x07:
                buffer << " [Interrupt: Machine timer interrupt]";
                break;
            case 0x08:
                buffer << " [Interrupt: User external interrupt]";
                break;
            case 0x09:
                buffer << " [Interrupt: Supervisor external interrupt]";
                break;
            case 0x0A:
                buffer << " [Interrupt: Hypervisor external interrupt]";
                break;
            case 0x0B:
                buffer << " [Interrupt: Machine external interrupt]";
                break;
            default:
                buffer << " [Unknown Interrupt]";
        }
    } else if (p.dst & 0x40) {
        // destination register
        const char* regName = NULL;
        if (p.dst & 0x20) {
            regName = fpr_name[p.dst & 0x1f];
        } else {
            regName = xpr_name[p.dst & 0x1f];
        }
        buffer << " [" << regName << " = 0x" << std::hex << p.data << "]";
    }
    switch (p.instruction & 0x7F) {
        case 0x03: // Load
        case 0x23: // Store
        case 0x2F: // AMO
        case 0x07: // FP-Load
        case 0x27: // FP-Store
            buffer << " (addr = 0x" << std::hex << p.addr << ")";
    }
    return buffer.str();
}

void PrintTrace::printStatus() {
    fprintf(stderr, "PrintTrace::printStatus() - %llu packets seen\n", (long long unsigned) packets);
    outBuffer.printToOStream(&std::cerr, 0);
}
