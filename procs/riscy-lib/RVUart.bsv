import ClientServer::*;
import RS232::*;
import Vector::*;
import GetPut::*;
import Vector::*;
import BuildVector::*;
import Ehr::*;


interface RVUart;
  // Internal connections
  interface UncachedMemServer memifc;
  method Action put (Bit#(8) data);
  method Maybe#(Bit#(8)) get;

  // external connections for rx/tx (to be connected to a UART
  method Action rx (Bit#(1) x);
  method Bit#(1) tx;
  method Bit#(16) divisor;
  method Vector#(cores, Bool) receiveInterrupt;
endinterface

module mkRVUart_RV32#(Integer divisor)(RVUart)
    provisos (NumAlias#(internalAddrSize, 8));
  // Layout of memory interface (mostly derived by SiFive Freedom E300)
  // Address   Name     Description
  // 0x0000    txData   Transmit data register
  // 0x0004    rxData   Receive data register
  // 0x0008    txCtrl   Transmit control register
  // 0x000C    rxCtrl   Receive control register
  // 0x0010    div      Baud rate divisor
  Bit#(internalAddrSize) txDataAddr = 'h0;
  Bit#(internalAddrSize) rxDataAddr = 'h4;
  Bit#(internalAddrSize) txCtrlAddr = 'h8;
  Bit#(internalAddrSize) rxCtrlAddr = 'hC;
  Bit#(internalAddrSize) divAddr    = 'h10;

  // TODO: Make a circular ring buffer for that we can then pass to connectal for
  //       memory mapped interface
  // ie. txDataRing 0x000 -> index_1[31:24], index_2[23:16], index_3[15:8], index_4[7:0]
  //     txTailPtr  0x004 -> ptr to whats next in the ring buffer
  Ehr#(2, Maybe#(Tuple2#(Bool, Bit#(internalAddrSize)))) pendingReq <- mkEhr(tagged Invalid);

  // BSV specific UART configuration
  // BSV UART implementation does a few things
  // its interface:
  // interface UART#(numeric type depth);
  //   interface RS232          rs232;
  //     method sout = rXmitDataOut;
  //     method sin  = rRecvData._write;
  //   interface Get#(Bit#(8))  tx;
  //     method ActionValue#(Bit#(8)) get;
  //   interface Put#(Bit#(8))  rx;
  //     method Action put(x)
  // Get and Put have FiFos attached to the ends of them
  UART#(16) uart <- mkUART(8, EVEN, STOP_1_5, divReg);
  // Data registers
  Reg#(Bit#(32)) txDataReg <- mkReg(0);
  Reg#(Bit#(32)) rxDataReg <- mkReg(0);
  Reg#(Bit#(32)) txCtrlReg <- mkReg(0);
  Reg#(Bit#(32)) rxCtrlReg <- mkReg(0);
  Reg#(Bit#(16)) divReg <- mkReg(divsor);

  Ehr#(2, Bool) interruptReg <- mkEhr(0);

  rule doTxData (txDataReg[31] && txCtrlReg[0]);
    // There is an implicit guard on the Fifo for uart.put
    uart.put(txDataReg[7:0]);
    txDataReg[31] <= 0;
  endrule

  rule doRxData (!rxDataReg[0] && rxCtrlReg[0]);
    rxDataReg <= uart.get;
    interruptReg[0] <= True;
  endrule

  interface UncachedMemServer memifc;
    interface Put request;
      method Action put(UncachedMemReq req) if (!isValid(pendingReq[1]));
        if (req.write) begin
          case (truncate(req.addr))
            txDataAddr: txDataReg <= req.data;
            rxDataAddr: rxDataReg <= req.data;
            txCtrlAddr: txCtrlReg  <= req.data;
            rxCtrlAddr: rxCtrlReg  <= req.data;
            // You shouldn't be able to write to the divAddr
            //divAddr:    divReg     <= req.data;
            default: noAction;
          endcase
          pendingReq[1] <= tagged Valid tuple2(True, truncate(req.addr));
        end else begin
          pendingReq[1] <= tagged Valid tuple2(False, truncate(req.addr));
        end
      endmethod
    endinterface
    interface Get response;
      method ActionValue#(UncachedMemResp) get if (pendingReq[0] matches tagged Valid .reqTuple);
        Bool write = tpl_1(reqTuple);
        Bit#(internalAddrSize) addr = tpl_2(reqTuple);
        Bit#(32) retVal = 0;
        case (truncate(addr))
          txDataAddr: retVal = txDataReg;
          rxDataAddr: retVal = rxDataReg;
          txCtrlAddr: retVal = txCtrlReg;
          rxCtrlAddr: retVal = rxCtrlReg;
          divAddr:    retVal = divReg;
          default:    retVal = 0;
        endcase
        pendingReq[0] <= tagged Invalid;
        return UncachedMemResp{ write: write, data: write? 0: retVal };
      endmethod
    endinterface
  endinterface

  method Action put(Bit#(8) data);
    if (txDataReg[31] && txCtrlReg[0]) begin
      txDataReg <= {1, '0, data};
    end
  endmethod

  method ActionValue#(Maybe#(Bit#(8))) get;
    Bit#(8) retVal = tagged Invalid;
    if (rxDataReg[31]) begin
      retVal = tagged Valid(rxDataReg[7:0]);
      if (rxCtrlReg[0]) begin
        rxDataReg <= 0;
      end
    end
    return retVal;
  endmethod

  method Action rx (Bit#(1) x) = uart.sin;
  method Bit#(1) tx = uart.sout;
  method Bit#(16) divisor = divReg;
  method Vector#(1, Bool) receiveInterrupt = vec(receiveInterrupt);

endmodule
