import Risc0.Lemmas

namespace Risc0.IsZero.Witness.Code

open MLIRNotation

def full : MLIRProgram :=
  "%0" ←ₐ .Const 1;
  "%1" ←ₐ .Get ⟨"in"⟩ 0 0;
  nondet (
    "%4" ←ₐ ??₀⟨"%1"⟩;
    ⟨"data"⟩[0] ←ᵢ ⟨"%4"⟩;
    "%5" ←ₐ Inv⟨"%1"⟩;
    ⟨"data"⟩[1] ←ᵢ ⟨"%5"⟩
  );
  "%2" ←ₐ .Get ⟨"data"⟩ 0 0;
  guard ⟨"%2"⟩ then (?₀ ⟨"%1"⟩);
  "%3" ←ₐ .Sub ⟨"%0"⟩ ⟨"%2"⟩;
  guard ⟨"%3"⟩ then ("%4" ←ₐ .Get ⟨"data"⟩ 0 1; "%5" ←ₐ .Mul ⟨"%1"⟩ ⟨"%4"⟩; "%6" ←ₐ .Sub ⟨"%5"⟩ ⟨"%0"⟩; ?₀ ⟨"%6"⟩)
def getReturn (st: State) (res_data: BufferAtTime) : Prop :=
  ((st.buffers ⟨"data"⟩ |>.get!.getLast!) = res_data)
∧ ¬ st.isFailed
def run (st: State) (res_data: BufferAtTime): Prop :=
  getReturn (full.runProgram st) res_data

end Code

def start_state (input_in: BufferAtTime) : State :=
  { buffers := Map.fromList [(⟨"in"⟩, [input_in]), (⟨"data"⟩, [[.none, .none]])]
  , felts := Map.empty
  , props := Map.empty
  , isFailed := false
  , bufferWidths := Map.fromList [(⟨"in"⟩, 1), (⟨"data"⟩, 2)]
  , cycle := 0
  , vars := [⟨"in"⟩, ⟨"data"⟩]
  }

end Risc0.IsZero.Witness
