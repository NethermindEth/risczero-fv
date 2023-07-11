import Risc0.Basic
import Risc0.Lemmas

namespace Risc0.OneHot2.Witness.Code

open MLIRNotation

def full : MLIRProgram :=
  "%0" ←ₐ .Const 1;
  "%1" ←ₐ .Const 0;
  "%2" ←ₐ .Get ⟨"code"⟩ 0 0;
  nondet (
    "%12" ←ₐ ??₀⟨"%2"⟩;
    ⟨"data"⟩[0] ←ᵢ ⟨"%12"⟩;
    "%13" ←ₐ .Sub ⟨"%2"⟩ ⟨"%0"⟩;
    "%14" ←ₐ ??₀⟨"%13"⟩;
    ⟨"data"⟩[1] ←ᵢ ⟨"%14"⟩
  );
  "%3" ←ₐ .Get ⟨"data"⟩ 0 1;
  "%4" ←ₐ .Sub ⟨"%3"⟩ ⟨"%2"⟩;
  ?₀ ⟨"%4"⟩;
  "%5" ←ₐ .Get ⟨"data"⟩ 0 0;
  "%6" ←ₐ .Sub ⟨"%0"⟩ ⟨"%5"⟩;
  "%7" ←ₐ .Mul ⟨"%5"⟩ ⟨"%6"⟩;
  ?₀ ⟨"%7"⟩;
  "%8" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩;
  "%9" ←ₐ .Mul ⟨"%3"⟩ ⟨"%8"⟩;
  ?₀ ⟨"%9"⟩;
  "%10" ←ₐ .Add ⟨"%5"⟩ ⟨"%3"⟩;
  "%11" ←ₐ .Sub ⟨"%10"⟩ ⟨"%0"⟩;
  ?₀ ⟨"%11"⟩
def getReturn (st: State) : BufferAtTime :=
  st.buffers ⟨"data"⟩ |>.get!.getLast!
def run (st: State) : BufferAtTime :=
  getReturn (full.runProgram st)

end Code

def start_state (input : BufferAtTime) : State :=
  { buffers := Map.fromList [(⟨"code"⟩, [input]), (⟨"data"⟩, [[none, none]])]
  , bufferWidths := Map.fromList [(⟨"code"⟩, 1), (⟨"data"⟩, 2)]
  , constraints := []
  , cycle := 0
  , felts := Map.empty
  , props := Map.empty
  , vars := [⟨"code"⟩, ⟨"data"⟩]
  , isFailed := false
  }

end Risc0.OneHot2.Witness
