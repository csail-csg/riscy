#ifndef DEVICES_HPP
#define DEVICES_HPP

#include <semaphore.h>

#include "spike/devices.h"

class emulated_uart_t : public abstract_device_t {
    public:
        bool load(reg_t addr, size_t len, uint8_t* bytes) {
            return false;
        }
        bool store(reg_t addr, size_t len, const uint8_t* bytes) {
            // if (addr == 0x40000020) {
            if (addr == 0x20) {
                std::cout << (char) bytes[0];
                return true;
            }
            return false;
        }
};

class exit_code_reg_t : public abstract_device_t {
    public:
        exit_code_reg_t() {
            sem_init(&writeSem, 0, 0);
        }
        ~exit_code_reg_t() {
            sem_destroy(&writeSem);
        }
        bool load(reg_t addr, size_t len, uint8_t* bytes) {
            return false;
        }
        bool store(reg_t addr, size_t len, const uint8_t* bytes) {
            if (addr == 0x00) {
                // cap len at 8 otherwise memcpy will overflow uint64_t
                if (len > 8) {
                    len = 8;
                }
                exit_code = 0;
                memcpy((void *) &exit_code, (const void*) bytes, len);
                sem_post(&writeSem);
                return true;
            } else {
                return false;
            }
        }
        uint64_t wait_for_exit_code() {
            sem_wait(&writeSem);
            return exit_code;
        }
    private:
        sem_t writeSem;
        uint64_t exit_code;
};

#endif
