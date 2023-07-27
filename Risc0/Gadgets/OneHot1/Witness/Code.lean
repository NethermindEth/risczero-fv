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
def getReturn (st: State) (res_data: BufferAtTime) : Prop :=
  ((st.buffers ⟨"data"⟩ |>.get!.getLast!) = res_data)
∧ ¬ st.isFailed
def run (st: State) (res_data: BufferAtTime): Prop :=
  getReturn (full.runProgram st) res_data

end Code

def start_state (input_code: BufferAtTime) : State :=
  { buffers := Map.fromList [(⟨"code"⟩, [input_code]), (⟨"data"⟩, [[.none]])]
  , felts := Map.empty
  , props := Map.empty
  , isFailed := false
  , bufferWidths := Map.fromList [(⟨"code"⟩, 1), (⟨"data"⟩, 1)]
  , cycle := 0
  , vars := [⟨"code"⟩, ⟨"data"⟩]
  }

end Risc0.OneHot1.Witness
