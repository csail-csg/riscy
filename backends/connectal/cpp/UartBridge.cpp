
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

#include "UartBridge.hpp"

UartBridge::UartBridge(unsigned int indicationId, unsigned int requestId) :
      UartBridgeIndicationWrapper(indicationId) {
    uartBridgeRequest = new UartBridgeRequestProxy(requestId);
    sem_init(&responseSem, 0, 0);
}

UartBridge::~UartBridge() {
  sem_destroy(&responseSem);
  delete uartBridgeRequest;
}

void UartBridge::put(const uint8_t character) {
  uartBridgeRequest->put(character);
}

void UartBridge::setDivisor(const uint16_t divisor) {
  uartBridgeRequest->setDivisor(divisor);
  sem_wait(&responseSem);
}

void UartBridge::get(const uint8_t character) {
  responseData = (uint32_t) character;
  printf("%c", character);
  fflush(stdout);
}

void UartBridge::setDivisorDone() {
  sem_post(&responseSem);
}
