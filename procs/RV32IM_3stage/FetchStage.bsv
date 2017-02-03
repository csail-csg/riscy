import RVTypes::*;
import CoreStates::*;
import GetPut::*;

interface FetchStage;
endinterface

typedef struct {
    Reg#(Maybe#(FetchState)) fs;
    Reg#(Maybe#(ExecuteState)) es;
    Put#(Addr) ifetchreq;
} FetchRegs;

module mkFetchStage#(FetchRegs fr)(FetchStage);
    let ifetchreq = fr.ifetchreq;

    rule doFetch(fr.fs matches tagged Valid .fetchState
                    &&& fr.es == tagged Invalid);
        // get and clear the fetch state
        let pc = fetchState.pc;
        fr.fs <= tagged Invalid;

        // request instruction
        ifetchreq.put(pc);

        // pass to execute state
        fr.es <= tagged Valid ExecuteState{ poisoned: False, pc: pc };
    endrule
endmodule
