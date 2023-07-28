import Risc0.Lemmas

namespace Risc0.OneHot2.Constraints.Code

open MLIRNotation

def full : MLIRProgram :=
  "%0" ←ₐ .Const 1;
  "%1" ←ₐ ⊤;
  "%2" ←ₐ .Get ⟨"code"⟩ 0 0;
  "%3" ←ₐ .Get ⟨"data"⟩ 0 1;
  "%4" ←ₐ .Sub ⟨"%3"⟩ ⟨"%2"⟩;
  "%5" ←ₐ ⟨"%1"⟩ &₀ ⟨"%4"⟩;
  "%6" ←ₐ .Get ⟨"data"⟩ 0 0;
  "%7" ←ₐ .Sub ⟨"%0"⟩ ⟨"%6"⟩;
  "%8" ←ₐ .Mul ⟨"%6"⟩ ⟨"%7"⟩;
  "%9" ←ₐ ⟨"%5"⟩ &₀ ⟨"%8"⟩;
  "%10" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩;
  "%11" ←ₐ .Mul ⟨"%3"⟩ ⟨"%10"⟩;
  "%12" ←ₐ ⟨"%9"⟩ &₀ ⟨"%11"⟩;
  "%13" ←ₐ .Add ⟨"%6"⟩ ⟨"%3"⟩;
  "%14" ←ₐ .Sub ⟨"%13"⟩ ⟨"%0"⟩;
  "%15" ←ₐ ⟨"%12"⟩ &₀ ⟨"%14"⟩
def getReturn (st: State) : Prop :=
  st.constraintsInVar ⟨"%15"⟩
def run (st: State) : Prop :=
  getReturn (full.runProgram st)

end Code

def start_state (input_code output_data: BufferAtTime) : State :=
  { buffers := Map.fromList [(⟨"code"⟩, [input_code]), (⟨"data"⟩, [output_data])]
  , felts := Map.empty
  , props := Map.empty
  , isFailed := false
  , bufferWidths := Map.fromList [(⟨"code"⟩, 1), (⟨"data"⟩, 2)]
  , cycle := 0
  , vars := [⟨"code"⟩, ⟨"data"⟩]
  }

end Risc0.OneHot2.Constraints
