
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

`include "ProcConfig.bsv"

import BuildVector::*;
import DefaultValue::*;
import ClientServer::*;
import Clocks::*;
import Connectable::*;
import FIFO::*;
import GetPut::*;
import Vector::*;

import ClientServerUtil::*;
import FIFOG::*;
import GenericAtomicMem::*;
import PolymorphicMem::*;
import Port::*;
import MemUtil::*;
import ServerUtil::*;

import Abstraction::*;
// import BasicMemorySystemBlocks::*;
// import BramIDMem::*;
import Core::*;
import ProcPins::*;
import RTC::*;
import RVUart::*;
import SPI::*;
import RVSPI::*;
import RVTypes::*;
import VerificationPacket::*;
import VerificationPacketFilter::*;

// This is used by ProcConnectal
typedef DataSz MainMemoryWidth;

// Multiple devices in mkProc can't be clock gated, so the mkProc module
// should not have the gate_all_clocks attribute.
(* synthesize *)
module mkProc(Proc#(DataSz));
    // Address map (some portions hard-coded in memory system
    // 0x0000_0000 - 0x2000_0000 : tightly coupled memory (not all used)
    // 0x2000_0000 - 0x2FFF_FFFF : rtc
    // 0x3000_0000 - 0x3FFF_FFFF : uart
    // 0x4000_0000 - 0xFFFF_FFFF : mmio

    let clock <- exposeCurrentClock();

`ifdef CONFIG_RV32
    RTC#(1, ByteEnMemServerPort#(32,2)) rtc <- mkRTC_RV32;
`else
    RTC#(1, ByteEnMemServerPort#(64,3)) rtc <- mkRTC_RV64;
`endif

    //   9600 baud: divisor = 26042
    // 115200 baud: divisor = 134
    RVUart#(ByteEnMemServerPort#(32,2)) uart_module <- mkRVUart_RV32(17);

    RVSPI#(ByteEnMemServerPort#(32,2)) spi_module <- mkRVSPI();

    Bool timer_interrupt = rtc.timerInterrupt[0];
    Bit#(64) timer_value = rtc.timerValue;

    Wire#(Bool) extInterruptWire <- mkDWire(False);

`ifdef CONFIG_IDMEM_INIT_HEX_FILE
    let sram <- mkPolymorphicBRAMLoad(64*1024/4, tagged Hex `CONFIG_IDMEM_INIT_HEX_FILE);
`else
    let sram <- mkPolymorphicBRAM(64*1024/4);
`endif

    // MMIO server for devices outside of the processor
    FIFOG#(CoarseMemReq#(32,2)) uncachedReqFIFO <- mkFIFOG;
    FIFOG#(CoarseMemResp#(2)) uncachedRespFIFO <- mkFIFOG;
    let mmio_server = toServerPort(uncachedReqFIFO, uncachedRespFIFO);
    let mmio_client = toClientPort(uncachedReqFIFO, uncachedRespFIFO);

    // numClients = 3
    // addrSz = 32
    // logNumBytes = 2
    MixedAtomicMemBus#(3, 32, 2) memBus <- mkMixedAtomicMemBus(vec(
            mixedMemBusItemFromAddrRange( 'h0000_0000, 'h1FFF_FFFF, tagged ByteEn sram ),
            mixedMemBusItemFromAddrRange( 'h2000_0000, 'h2FFF_FFFF, tagged ByteEn rtc.memifc ),
            mixedMemBusItemFromAddrRange( 'h3000_0000, 'h3000_FFFF, tagged ByteEn uart_module.memifc ),
            mixedMemBusItemFromAddrRange( 'h3001_0000, 'h3001_FFFF, tagged ByteEn spi_module.memifc ),
            mixedMemBusItemFromAddrRange( 'h4000_0000, 'h7FFF_FFFF, tagged Coarse mmio_server ),
            mixedMemBusItemFromAddrRange( 'h8000_0000, 'hFFFF_FFFF, tagged Coarse mmio_server )));

    ReadOnlyMemServerPort#(32, 2) imem = simplifyMemServerPort(memBus.clients[0]);

    Core#(32) core <- mkThreeStageCore(
                    imem,
                    memBus.clients[1],
                    False, // inter-process interrupt
                    timer_interrupt, // timer interrupt
                    timer_value, // timer value
                    extInterruptWire, // external interrupt
                    0); // hart ID

    // Processor Control
    method Action start();
        core.start(0);
    endmethod
    method Action stop();
        core.stop;
    endmethod

    // Verification
    method Maybe#(VerificationPacket) currVerificationPacket;
        return core.currVerificationPacket;
    endmethod

    // Main Memory Connection
    interface CoarseMemClientPort ram = nullClientPort;

    interface CoarseMemServerPort mmio = mmio_client;

    interface CoarseMemServerPort extmem = simplifyMemServerPort(memBus.clients[2]);

    // Interrupts
    method Action triggerExternalInterrupt;
        extInterruptWire <= True;
    endmethod

    method Action stallPipeline(Bool stall);
        core.stallPipeline(stall);
    endmethod

    interface ProcPins pins;
        // no other pins connected at the moment
        `ifdef CONFIG_RS232
            interface RS232 uart = uart_module.uart_pins;
        `endif
        `ifdef CONFIG_SPI
            interface SPIMasterPins spi = spi_module.spi_pins;
        `endif
        interface Clock deleteme_unused_clock = clock;
    endinterface
endmodule
