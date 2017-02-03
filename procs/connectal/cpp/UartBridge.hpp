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
