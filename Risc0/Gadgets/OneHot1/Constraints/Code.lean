import Risc0.Cirgen
import Risc0.Lemmas

namespace Risc0.OneHot1.Constraints.Code

open MLIRNotation

def full : MLIRProgram :=
  "%0" ←ₐ .Const 0;
  "%1" ←ₐ .Const 1;
  "%2" ←ₐ ⊤;
  "%3" ←ₐ .Get ⟨"code"⟩ 0 0;
  "%4" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩;
  "%5" ←ₐ ⟨"%2"⟩ &₀ ⟨"%4"⟩;
  "%6" ←ₐ .Get ⟨"data"⟩ 0 0;
  "%7" ←ₐ .Sub ⟨"%1"⟩ ⟨"%6"⟩;
  "%8" ←ₐ .Mul ⟨"%6"⟩ ⟨"%7"⟩;
  "%9" ←ₐ ⟨"%5"⟩ &₀ ⟨"%8"⟩;
  "%10" ←ₐ .Sub ⟨"%6"⟩ ⟨"%1"⟩;
  "%11" ←ₐ ⟨"%9"⟩ &₀ ⟨"%10"⟩
def getReturn (st: State) : Prop :=
  st.constraintsInVar ⟨"%11"⟩
def run (st: State) : Prop :=
  getReturn (full.runProgram st)

end Code

def start_state (input data : BufferAtTime) : State :=
  { buffers := Map.fromList [(⟨"code"⟩, [input]), (⟨"data"⟩, [data])]
  , bufferWidths := Map.fromList [(⟨"code"⟩, 1), (⟨"data"⟩, 1)]
  , constraints := []
  , cycle := 0
  , felts := Map.empty
  , props := Map.empty
  , vars := [⟨"code"⟩, ⟨"data"⟩]
  , isFailed := false
  }

end Risc0.OneHot1.Constraints
