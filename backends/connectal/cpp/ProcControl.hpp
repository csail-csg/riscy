
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

#ifndef PROC_CONTROL_HPP
#define PROC_CONTROL_HPP

#include <semaphore.h>
#include "ProcControlIndication.h"
#include "ProcControlRequest.h"
#include "GeneratedTypes.h"

class ProcControl : public ProcControlIndicationWrapper {
    public:
        ProcControl(unsigned int indicationId, unsigned int requestId);
        ~ProcControl();

        // these are called by the main thread
        void reset();
        void start(const uint64_t startPc);
        void stop();
        void configure(const uint32_t sharedMemRefPointer, const uint64_t externalMMIOBaseAddr);

        // this sets the verification packet settings for the next time start
        // is called
        void configureVerificationPackets(const uint64_t verificationPacketsToIgnoreIn, const bool sendSynchronizationPacketsIn);

        // called by ProcControlIndication thread
        void resetDone();

    private:
        // only used by main thread
        ProcControlRequestProxy *procControlRequest;
        uint64_t verificationPacketsToIgnore;
        bool sendSynchronizationPackets;

        // used by both threads
        sem_t resetSem;
};

#endif
