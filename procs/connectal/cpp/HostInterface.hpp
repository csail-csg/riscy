
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

#ifndef HOST_INTERFACE_HPP
#define HOST_INTERFACE_HPP

#include <semaphore.h>
#include <queue>
#include "HostInterfaceIndication.h"
#include "HostInterfaceRequest.h"
#include "GeneratedTypes.h"

class HostInterface : public HostInterfaceIndicationWrapper {
    public:
        HostInterface(unsigned int indicationId, unsigned int requestId);
        ~HostInterface();

        // called by HostInterfaceIndication thread
        void toHost(const uint64_t v);

        // called by the main thread to access tohost/fromhost
        bool getToHostMessage(uint64_t *msg);
        void putFromHostMessage(uint64_t msg);

    private:
        // only used by main thread
        HostInterfaceRequestProxy *hostInterfaceRequest;

        // used by both threads
        std::queue<uint64_t> toHostMessages;
        pthread_mutex_t mutex;
};

#endif
