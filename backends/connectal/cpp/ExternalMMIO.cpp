
// Copyright (c) 2016, 2017 Massachusetts Institute of Technology

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

#include <iostream>
#include "ExternalMMIO.hpp"

ExternalMMIO::ExternalMMIO(unsigned int requestId, unsigned int responseId) : ExternalMMIORequestWrapper(requestId) {
    externalMMIOResponse = new ExternalMMIOResponseProxy(responseId);
    pthread_mutex_init(&mutex, 0);
}

void ExternalMMIO::addDevice(const uint64_t addr, abstract_device_t* device) {
    bus.add_device((reg_t) addr, device);
}

void ExternalMMIO::triggerInterrupt() {
    externalMMIOResponse->triggerExternalInterrupt();
}

void ExternalMMIO::request(const int write, const uint64_t addr, const uint64_t data) {
    // get mutex
    pthread_mutex_lock(&mutex);
    // forward request to device
    uint64_t respData = 0;
    bool success = false;
    if (write == 0) {
#ifdef CONFIG_RV64
        success = bus.load((reg_t) addr, 8, (uint8_t*) &respData);
#else
        success = bus.load((reg_t) addr, 4, (uint8_t*) &respData);
#endif
    } else {
#ifdef CONFIG_RV64
        success = bus.store((reg_t) addr, 8, (uint8_t*) &data);
#else
        success = bus.store((reg_t) addr, 4, (uint8_t*) &data);
#endif
    }
    if (!success) {
        if (write == 0) {
            std::cerr << "[ERROR] MMIO read failed, addr = 0x" << std::hex << addr << std::endl;
        } else {
            std::cerr << "[ERROR] MMIO write failed, addr = 0x" << std::hex << addr << ", data = 0x" << std::hex << data << std::endl;
        }
    }
    // forward response to processor
    externalMMIOResponse->response(write, respData);
    // release mutex
    pthread_mutex_unlock(&mutex);
}
