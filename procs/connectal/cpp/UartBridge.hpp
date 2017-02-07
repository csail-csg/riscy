
// Copyright (c) 2017 Massachusetts Institute of Technology

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

#ifndef UART_BRIDGE_HPP
#define UART_BRIDGE_HPP

#include <semaphore.h>
#include "UartBridgeIndication.h"
#include "UartBridgeRequest.h"
#include "GeneratedTypes.h"

class UartBridge : public UartBridgeIndicationWrapper {
  public:
    UartBridge(unsigned int indicationId, unsigned int requestId);
    ~UartBridge();

    // these are called by the main thread
    void put(const uint8_t character);
    void setDivisor(const uint16_t divisor);
    void get(const uint8_t character);
    void setDivisorDone();

  private:
    sem_t responseSem;
    uint32_t responseData;

    UartBridgeRequestProxy *uartBridgeRequest;
};
#endif
