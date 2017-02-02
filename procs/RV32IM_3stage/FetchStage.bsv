import ClientServer::*;
import RVTypes::*;
import CoreStates::*;
import GetPut::*;

interface FetchStage;
endinterface

typedef struct {
    Reg#(Maybe#(FetchState)) fs;
    Reg#(Maybe#(ExecuteState)) es;
    Server#(Addr, Instruction) ifetch;
} FetchRegs;

module mkFetchStage#(FetchRegs fr)(FetchStage);
    //let fs = fr.fs;
    //let es = fr.es;
    let ifetch = fr.ifetch;

    rule doFetch(fr.fs matches tagged Valid .fetchState
                    &&& fr.es == tagged Invalid);
        // get and clear the fetch state
        let pc = fetchState.pc;
        fr.fs <= tagged Invalid;

        // request instruction
        ifetch.request.put(pc);

        // pass to execute state
        fr.es <= tagged Valid ExecuteState{ poisoned: False, pc: pc };
    endrule
endmodule
