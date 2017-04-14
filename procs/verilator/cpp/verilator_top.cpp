#include <iostream>

#include <verilated.h>
#include "verilated_vcd_c.h"

#include "VmkProcVerilator.h"

// #define DO_TRACE


VmkProcVerilator* top = NULL;
VerilatedVcdC* tfp = NULL;
uint64_t main_time = 0;

void tick() {
    top->CLK = 0;
    top->eval();
#ifdef DO_TRACE
    tfp->dump(main_time);
#endif
    top->CLK = 1;
    top->eval();
#ifdef DO_TRACE
    tfp->dump(main_time);
#endif
    main_time++;
}
void tick(int n) {
    for(int i = 0; i < n; i++) {
        tick();
    }
}

void methodCall( uint8_t& rdy, uint8_t& en ) {
    // set en to 0
    en = 0;
    // wait until rdy is 1
    while (rdy == 0) {
        tick();
    }
    // set en to 1 for one cycle
    en = 1;
    tick();
    // set en to 0
    en = 0;
}

uint8_t getBit( uint32_t* base, uint32_t bit ) {
    while (bit >= 32) {
        base++;
        bit -= 32;
    }
    return ((*base) >> bit) & 1;
}
uint64_t getBits( uint32_t* base, uint32_t high, uint32_t low ) {
    uint64_t ret = 0;
    for (int i = high ; i >= (int) low ; i--) {
        ret = (ret << 1) | (uint64_t) getBit(base, i);
    }
    return ret;
}

int main(int argc, char* argv[]) {
    Verilated::commandArgs(argc, argv);
#ifdef DO_TRACE
    Verilated::traceEverOn(true);
#else
    Verilated::traceEverOn(false);
#endif

    top = new VmkProcVerilator();

#ifdef DO_TRACE
    VerilatedVcdC* tfp = new VerilatedVcdC();
    top->trace(tfp, 99);
    tfp->open("trace.vcd");
#endif

    top->RST_N = 0;
    tick(5);
    top->RST_N = 1;
    tick(5);

    std::cout << "Starting processor..." << std::endl;
    methodCall(top->RDY_start, top->EN_start);
    std::cout << "Processor started!" << std::endl;

    while (!Verilated::gotFinish()) {
        tick();
        // get PC from verification packet:
        // if (top->RDY_currVerificationPacket == 1) {
        //     if (getBit(top->currVerificationPacket, 301) == 1) {
        //         uint64_t pc = getBits(top->currVerificationPacket, 236, 173);
        //     }
        // }
    }

    top->final();
#ifdef DO_TRACE
    tfp->close();
#endif

    delete top;
    return 0;
}
