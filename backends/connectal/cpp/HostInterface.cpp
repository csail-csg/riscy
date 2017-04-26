
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

#include "HostInterface.hpp"

HostInterface::HostInterface(unsigned int indicationId, unsigned int requestId) : HostInterfaceIndicationWrapper(indicationId) {
    hostInterfaceRequest = new HostInterfaceRequestProxy(requestId);
    pthread_mutex_init(&mutex, 0);
}

HostInterface::~HostInterface() {
    pthread_mutex_lock(&mutex);
    pthread_mutex_destroy(&mutex);
    delete hostInterfaceRequest;
}

void HostInterface::toHost(const uint64_t v) {
    // enqueue v to the toHostMessages queue
    // fprintf(stderr, "%s:%d HostInterface::toHost(%d) starting\n", __FILE__, __LINE__, (int) v);
    pthread_mutex_lock(&mutex);
    toHostMessages.push(v);
    pthread_mutex_unlock(&mutex);
    // fprintf(stderr, "%s:%d HostInterface::toHost(%d) finishing\n", __FILE__, __LINE__, (int) v);
}

bool HostInterface::getToHostMessage(uint64_t *msg) {
    // try to dequeue a message from the toHostMessages queue
    // fprintf(stderr, "%s:%d HostInterface::getToHostMessage starting\n", __FILE__, __LINE__);
    bool foundMsg = false;
    pthread_mutex_lock(&mutex);
    if (!toHostMessages.empty()) {
        foundMsg = true;
        *msg = toHostMessages.front();
        toHostMessages.pop();
    } else {
        // default tohost value is 0
        *msg = 0;
    }
    pthread_mutex_unlock(&mutex);
    /*
    if (foundMsg) {
        fprintf(stderr, "%s:%d HostInterface::getToHostMessage finished, msg = %d\n", __FILE__, __LINE__, (int) *msg);
    } else {
        fprintf(stderr, "%s:%d HostInterface::getToHostMessage finished, no msg found\n", __FILE__, __LINE__);
    }
    */
    return foundMsg;
}

void HostInterface::putFromHostMessage(uint64_t msg) {
    // fprintf(stderr, "%s:%d HostInterface::gromHostMessage(%d)\n", __FILE__, __LINE__, (int) msg);
    hostInterfaceRequest->fromHost(msg);
}

