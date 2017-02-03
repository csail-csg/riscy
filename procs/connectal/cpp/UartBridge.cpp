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
