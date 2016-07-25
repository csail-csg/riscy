
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
#include "SpikeTandemVerifier.hpp"

SpikeTandemVerifier::SpikeTandemVerifier(std::vector<std::string> htifArgsIn, size_t memSzIn)
        : TandemVerifier(), htifArgs(htifArgsIn), memSz(memSzIn), sim(NULL), disassembler(new disassembler_t(64)), packets(0), instructions(0), abort(false), outBuffer(40) {
    pthread_mutex_init(&mutex, 0);
}

SpikeTandemVerifier::~SpikeTandemVerifier() {
    pthread_mutex_lock(&mutex);
    if (sim != NULL) {
        delete sim;
    }
    delete disassembler;
    pthread_mutex_destroy(&mutex);
}

bool SpikeTandemVerifier::checkVerificationPacket(VerificationPacket packet) {
    pthread_mutex_lock(&mutex);
    // init simulator if necessary
    if (sim == NULL) {
        initSim();
    }

    // fast forward to make up for skipped packets
    if (packet.skippedPackets > 0) {
        instructions += sim->get_core(0)->step_synchronize(packet.skippedPackets);
    }

    // set CSRs if necessary
    synchronize(packet);

    bool forceTrap = false;
    uint64_t forceTrapCause = 0;
    if (packet.trap) {
        // timer interrupt
        if (packet.trapType == 0x81) {
            forceTrap = true;
            forceTrapCause = (1ULL << 63) | 1;
        }
        // host interrupt
        if (packet.trapType == 0x82) {
            forceTrap = true;
            forceTrapCause = (1ULL << 63) | 2;
            // TODO: make sure spike's HTIF sees the host interrupt
        }
    }

    VerificationPacket spikePacket = packet;
    if (forceTrap) {
        // verification packet from the processor corresponds to a forced trap
        sim->get_core(0)->force_trap(forceTrapCause);
        // TODO: update spikePacket to include some things from the forced trap
        spikePacket.nextPc = sim->get_core(0)->get_state()->pc;
    } else {
        spikePacket = synchronizedSimStep(packet);
    }

    packets++;
    bool match = comparePackets(packet, spikePacket);

    if (!match) {
        errors++;
        std::ostringstream buffer;
        buffer << "[ERROR] Verification error in packet " << packets << " (instruction " << instructions << ")" << std::endl;
        buffer << "  [PROC]  " << verificationPacketToString(packet) << std::endl;
        buffer << "  [SPIKE] " << verificationPacketToString(spikePacket);
        outBuffer.addLine(buffer.str());
        outBuffer.printToOStream(&std::cerr, 20);
    } else {
        outBuffer.addLine(verificationPacketToString(packet));
        // fprintf(stderr, "%s\n", verificationPacketToString(packet).c_str());
    }

    // XXX: this was to temporarily print everything
    // outBuffer.printToOStream(&std::cerr, 20000);

    if (errors > 40) {
        abort = true;
        // and let's abort!
        exit(1);
    }
    pthread_mutex_unlock(&mutex);

    return match;
}

bool SpikeTandemVerifier::shouldAbort() {
    // // XXX: Should we do this? Does this work?
    // bool abort_read = false;
    // pthread_mutex_lock(&mutex);
    // abort_read = abort;
    // pthread_mutex_unlock(&mutex);
    // return abort_read;
    return abort;
}

void SpikeTandemVerifier::synchronize(VerificationPacket packet) {
    // TODO: implement this for priv spec v1.9
}

void SpikeTandemVerifier::initSim() {
    sim = new sim_t("RV64IMAFD", 1 /* cores */, memSz >> 20, true /* halted */, htifArgs);
    // sim->start() calls htif_t's start implementation.
    // this loads the program and resets the processor.
    sim->start();
}

VerificationPacket SpikeTandemVerifier::synchronizedSimStep(VerificationPacket packet) {
    VerificationPacket spikePacket;

    // get pc and instruction for spikePacket
    if (instructions > 0) {
        spikePacket.pc = sim->get_core(0)->get_state()->pc;
    } else {
        // if no instructions have been retired yet, assume spike starts at
        // address 0x1000
        spikePacket.pc = 0x1000;
    }
    try {
        spikePacket.instruction = sim->get_core(0)->get_mmu()->load_uint32(spikePacket.pc);
    } catch (trap_t& t) {
        spikePacket.instruction = packet.instruction;
    }

    // perform the step
    bool instructionRetired = sim->get_core(0)->try_step_synchronize();

    // form the rest of spikePacket
    // -nextPc
    spikePacket.nextPc = sim->get_core(0)->get_state()->pc;
    // -trap and -trapType
    if (instructionRetired) {
        // this instruction executed successfully and did not result in a trap
        instructions++;
        spikePacket.trap = false;
        spikePacket.trapType = 0;
    } else {
        // this instruction caused a trap
        spikePacket.trap = true;
        // get trap type in compressed format used in verification packets
        reg_t cause = 0;
        if (sim->get_core(0)->get_state()->prv == PRV_S) {
            cause = sim->get_core(0)->get_state()->scause;
        } else {
            cause = sim->get_core(0)->get_state()->mcause;
        }
        if (cause & 0x8000000000000000ULL) {
            spikePacket.trapType = 0x80 | (cause & 0x7F);
        } else {
            spikePacket.trapType = cause & 0x7F;
        }
    }
    // -dst and data
    // TODO: fix this
    if (spikePacket.instruction == packet.instruction) {
        spikePacket.dst = packet.dst;
        if (spikePacket.dst & 0x40) {
            if (spikePacket.dst & 0x20) {
                // FPR
                spikePacket.data = sim->get_core(0)->get_state()->FPR[spikePacket.dst & 0x1F];
            } else {
                // XPR
                spikePacket.data = sim->get_core(0)->get_state()->XPR[spikePacket.dst & 0x1F];
            }
        } else {
            // data doesn't matter
            spikePacket.data = packet.data;
        }
    } else {
        spikePacket.dst = 0;
        spikePacket.data = 0;
    }

    return spikePacket;
}

bool SpikeTandemVerifier::comparePackets(VerificationPacket procP, VerificationPacket spikeP) {
    bool match = true;
    match = match && (procP.pc == spikeP.pc);
    match = match && (procP.nextPc == spikeP.nextPc);
    match = match && (procP.instruction == spikeP.instruction);
    match = match && (procP.trap == spikeP.trap);
    if (procP.trap) {
        match = match && (procP.trapType == spikeP.trapType);
    } else {
        match = match && (procP.dst == spikeP.dst);
        match = match && (procP.data == spikeP.data);
    }
    return match;
}

std::string SpikeTandemVerifier::verificationPacketToString(VerificationPacket p) {
    std::ostringstream buffer;
    // pc
    buffer << "0x" << std::setfill('0') << std::setw(8) << std::hex << p.pc << ": ";
    // instruction data
    buffer << "(0x" << std::setfill('0') << std::setw(8) << std::hex << p.instruction << ") ";
    // instruction disassembled
    std::string assembly = (disassembler->disassemble(p.instruction));
    buffer << std::left << std::setfill(' ') << std::setw(32) << assembly;

    if (p.trap) {
        switch (p.trapType) {
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
            case 0x80:
                buffer << " [Interrupt: Software interrupt]";
                break;
            case 0x81:
                buffer << " [Interrupt: Timer interrupt]";
                break;
            case 0x82:
                buffer << " [Interrupt: Host interrupt]";
                break;
            default:
                buffer << " [Unknown Trap]";
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

void SpikeTandemVerifier::printStatus() {
    fprintf(stderr, "SpikeTandemVerifier::printStatus() - %llu packets seen, %llu errors seen\n", (long long unsigned) packets, (long long unsigned) errors);
    outBuffer.printToOStream(&std::cerr, 0);
}
