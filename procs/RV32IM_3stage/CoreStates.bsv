import RVTypes::*;

typedef struct {
    Addr pc;
} FetchState deriving (Bits, Eq, FShow);

typedef struct {
    Bool poisoned;
    Addr pc;
} ExecuteState deriving (Bits, Eq, FShow);

typedef struct {
    Addr              pc;
    Maybe#(TrapCause) trap;
    RVDecodedInst     dInst;
    Addr              addr;
    Data              data;
} WriteBackState deriving (Bits, Eq, FShow);
