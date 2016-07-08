
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

#ifndef NULL_TANDEM_VERIFIER_HPP
#define NULL_TANDEM_VERIFIER_HPP

#include <inttypes.h>
#include <fstream>
#include "CircularBuffer.hpp"
#include "TandemVerifier.hpp"

class NullTandemVerifier : public TandemVerifier {
    public:
        NullTandemVerifier() : TandemVerifier(), outBuffer(40) {
            packets = 0;
        }
        ~NullTandemVerifier() {
        }
        bool checkVerificationPacket(VerificationPacket p) {
            packets++;
            lastPc = p.pc;
            std::ostringstream buffer;
            buffer << "0x" << std::hex << p.pc;
            outBuffer.addLine(buffer.str());
            return true;
        }
        void printStatus() {
            fprintf(stderr, "NullTandemVerifier::printStatus() - %llu packets seen. Last pc = 0x%llx\n", (long long unsigned) packets, (long long int) lastPc);
            outBuffer.printToOStream(&std::cerr, 0);
        }
    private:
        std::string verificationPacketToString(VerificationPacket p);
        CircularBuffer outBuffer;
        uint64_t packets;
        uint64_t lastPc;
};

#endif // TANDEM_VERIFIER_HPP
