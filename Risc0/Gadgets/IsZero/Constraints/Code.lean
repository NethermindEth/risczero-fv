import Risc0.Cirgen
import Risc0.Lemmas

namespace Risc0.IsZero.Constraints.Code

open MLIRNotation

def full : MLIRProgram :=
  "%0" ←ₐ .Const 1;
  "%1" ←ₐ ⊤;
  "%2" ←ₐ .Get ⟨"in"⟩ 0 0;
  "%3" ←ₐ .Get ⟨"data"⟩ 0 0;
  "%4" ←ₐ ⟨"%1"⟩ &₀ ⟨"%2"⟩;
  "%5" ←ₐ guard ⟨"%3"⟩ & ⟨"%1"⟩ with ⟨"%4"⟩;
  "%6" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩;
  "%7" ←ₐ .Get ⟨"data"⟩ 0 1;
  "%8" ←ₐ .Mul ⟨"%2"⟩ ⟨"%7"⟩;
  "%9" ←ₐ .Sub ⟨"%8"⟩ ⟨"%0"⟩;
  "%10" ←ₐ ⟨"%1"⟩ &₀ ⟨"%9"⟩;
  "%11" ←ₐ guard ⟨"%6"⟩ & ⟨"%5"⟩ with ⟨"%10"⟩
def getReturn (st: State) : Prop :=
  st.constraintsInVar ⟨"%11"⟩
def run (st: State) : Prop :=
  getReturn (full.runProgram st)

end Code

def start_state (input data : BufferAtTime) : State :=
  { buffers := Map.fromList [(⟨"in"⟩, [input]), (⟨"data"⟩, [data])]
  , bufferWidths := Map.fromList [(⟨"in"⟩, 1), (⟨"data"⟩, 2)]
  , constraints := []
  , cycle := 0
  , felts := Map.empty
  , props := Map.empty
  , vars := [⟨"in"⟩, ⟨"data"⟩]
  , isFailed := false
  }

end Risc0.IsZero.Constraints
