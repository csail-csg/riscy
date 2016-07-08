
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

#ifndef SPIKE_TANDEM_VERIFIER_HPP
#define SPIKE_TANDEM_VERIFIER_HPP

#include <string>
#include <vector>
#include <pthread.h>
#include "spike/sim.h"
#include "spike/disasm.h"
#include "CircularBuffer.hpp"
#include "TandemVerifier.hpp"

class SpikeTandemVerifier : public TandemVerifier {
    public:
        SpikeTandemVerifier(std::vector<std::string> htifArgsIn, size_t memSzIn);
        ~SpikeTandemVerifier();

        // called by VerificationIndication
        bool checkVerificationPacket(VerificationPacket p);
        bool shouldAbort();

        // called by main thread (probably?)
        void printStatus();

    private:
        void initSim();
        void synchronize(VerificationPacket p);
        VerificationPacket synchronizedSimStep(VerificationPacket p);
        bool comparePackets(VerificationPacket procP, VerificationPacket spikeP);
        std::string verificationPacketToString(VerificationPacket p);

        std::vector<std::string> htifArgs;
        size_t memSz;
        sim_t *sim;
        disassembler_t *disassembler;
        pthread_mutex_t mutex;

        // number of packets seen
        unsigned int packets;
        // number of instructions retired
        unsigned int instructions;
        // if too many errors have been seen
        bool abort;
        
        CircularBuffer outBuffer;
};

#endif
