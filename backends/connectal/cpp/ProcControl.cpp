
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

#include "ProcControl.hpp"

ProcControl::ProcControl(unsigned int indicationId, unsigned int requestId) :
        ProcControlIndicationWrapper(indicationId),
        verificationPacketsToIgnore(0),
        sendSynchronizationPackets(false) {
    procControlRequest = new ProcControlRequestProxy(requestId);
    sem_init(&resetSem, 0, 0);
}

ProcControl::~ProcControl() {
    sem_destroy(&resetSem);
    delete procControlRequest;
}

// TODO: only configure the processor in one place
void ProcControl::reset() {
    // request for the processor to reset
    procControlRequest->reset();
    // wait for reset to finish
    sem_wait(&resetSem);
}

// configure and start
void ProcControl::start(const uint64_t startPc) {
    procControlRequest->start(startPc, verificationPacketsToIgnore, (int) sendSynchronizationPackets);
}

void ProcControl::stop() {
    procControlRequest->stop();
}

void ProcControl::configureVerificationPackets(const uint64_t verificationPacketsToIgnoreIn, const bool sendSynchronizationPacketsIn) {
    verificationPacketsToIgnore = verificationPacketsToIgnoreIn;
    sendSynchronizationPackets = sendSynchronizationPacketsIn;
}

void ProcControl::resetDone() {
    // signal that reset is done
    sem_post(&resetSem);
}
