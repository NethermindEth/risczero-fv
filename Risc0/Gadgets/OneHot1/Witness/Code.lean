import Risc0.Basic
import Risc0.Lemmas

namespace Risc0.OneHot1.Witness.Code

open MLIRNotation

def full : MLIRProgram :=
  "%0" ←ₐ .Const 1;
  "%1" ←ₐ .Const 0;
  "%2" ←ₐ .Get ⟨"code"⟩ 0 0;
  nondet (
    "%8" ←ₐ ??₀⟨"%2"⟩;
    ⟨"data"⟩[0] ←ᵢ ⟨"%8"⟩
  );
  "%3" ←ₐ .Sub ⟨"%1"⟩ ⟨"%2"⟩;
  ?₀ ⟨"%3"⟩;
  "%4" ←ₐ .Get ⟨"data"⟩ 0 0;
  "%5" ←ₐ .Sub ⟨"%0"⟩ ⟨"%4"⟩;
  "%6" ←ₐ .Mul ⟨"%4"⟩ ⟨"%5"⟩;
  ?₀ ⟨"%6"⟩;
  "%7" ←ₐ .Sub ⟨"%4"⟩ ⟨"%0"⟩;
  ?₀ ⟨"%7"⟩
def getReturn (st: State) : BufferAtTime :=
  st.buffers ⟨"data"⟩ |>.get!.getLast!
def run (st: State) : BufferAtTime :=
  getReturn (full.runProgram st)

end Code

def start_state (input : BufferAtTime) : State :=
  { buffers := Map.fromList [(⟨"code"⟩, [input]), (⟨"data"⟩, [[none]])]
  , bufferWidths := Map.fromList [(⟨"code"⟩, 1), (⟨"data"⟩, 1)]
  , constraints := []
  , cycle := 0
  , felts := Map.empty
  , props := Map.empty
  , vars := [⟨"code"⟩, ⟨"data"⟩]
  , isFailed := false
  }

end Risc0.OneHot1.Witness
