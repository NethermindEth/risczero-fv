import Risc0.Basic
import Risc0.Lemmas

namespace Risc0.ComputeDecode.Constraints.Code

open MLIRNotation

def full : MLIRProgram :=
  "%0" ←ₐ .Const 128;
  "%1" ←ₐ .Const 16;
  "%2" ←ₐ .Const 8;
  "%3" ←ₐ .Const 2;
  "%4" ←ₐ .Const 4;
  "%5" ←ₐ .Const 64;
  "%6" ←ₐ ⊤;
  "%7" ←ₐ .Get ⟨"in"⟩ 0 0;
  "%8" ←ₐ .Get ⟨"in"⟩ 0 1;
  "%9" ←ₐ .Get ⟨"in"⟩ 0 2;
  "%10" ←ₐ .Get ⟨"in"⟩ 0 3;
  "%11" ←ₐ .Get ⟨"data"⟩ 0 13;
  "%12" ←ₐ .Get ⟨"data"⟩ 0 0;
  "%13" ←ₐ .Get ⟨"data"⟩ 0 8;
  "%14" ←ₐ .Mul ⟨"%13"⟩ ⟨"%4"⟩;
  "%15" ←ₐ .Get ⟨"data"⟩ 0 9;
  "%16" ←ₐ .Mul ⟨"%15"⟩ ⟨"%2"⟩;
  "%17" ←ₐ .Get ⟨"data"⟩ 0 1;
  "%18" ←ₐ .Mul ⟨"%17"⟩ ⟨"%1"⟩;
  "%19" ←ₐ .Add ⟨"%18"⟩ ⟨"%16"⟩;
  "%20" ←ₐ .Add ⟨"%19"⟩ ⟨"%14"⟩;
  "%21" ←ₐ .Add ⟨"%20"⟩ ⟨"%12"⟩;
  "%22" ←ₐ .Get ⟨"data"⟩ 0 10;
  "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%5"⟩;
  "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%21"⟩;
  "%25" ←ₐ .Mul ⟨"%24"⟩ ⟨"%3"⟩;
  "%26" ←ₐ .Add ⟨"%25"⟩ ⟨"%11"⟩;
  "%27" ←ₐ .Sub ⟨"%10"⟩ ⟨"%26"⟩;
  "%28" ←ₐ ⟨"%6"⟩ &₀ ⟨"%27"⟩;
  "%29" ←ₐ .Get ⟨"data"⟩ 0 3;
  "%30" ←ₐ .Get ⟨"data"⟩ 0 4;
  "%31" ←ₐ .Mul ⟨"%30"⟩ ⟨"%4"⟩;
  "%32" ←ₐ .Get ⟨"data"⟩ 0 11;
  "%33" ←ₐ .Get ⟨"data"⟩ 0 2;
  "%34" ←ₐ .Mul ⟨"%33"⟩ ⟨"%3"⟩;
  "%35" ←ₐ .Get ⟨"data"⟩ 0 12;
  "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%2"⟩;
  "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%34"⟩;
  "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%32"⟩;
  "%39" ←ₐ .Mul ⟨"%38"⟩ ⟨"%1"⟩;
  "%40" ←ₐ .Add ⟨"%39"⟩ ⟨"%31"⟩;
  "%41" ←ₐ .Add ⟨"%40"⟩ ⟨"%29"⟩;
  "%42" ←ₐ .Sub ⟨"%9"⟩ ⟨"%41"⟩;
  "%43" ←ₐ ⟨"%28"⟩ &₀ ⟨"%42"⟩;
  "%44" ←ₐ .Get ⟨"data"⟩ 0 6;
  "%45" ←ₐ .Get ⟨"data"⟩ 0 7;
  "%46" ←ₐ .Mul ⟨"%45"⟩ ⟨"%4"⟩;
  "%47" ←ₐ .Get ⟨"data"⟩ 0 5;
  "%48" ←ₐ .Get ⟨"data"⟩ 0 15;
  "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩;
  "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩;
  "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%1"⟩;
  "%52" ←ₐ .Get ⟨"data"⟩ 0 14;
  "%53" ←ₐ .Mul ⟨"%52"⟩ ⟨"%0"⟩;
  "%54" ←ₐ .Add ⟨"%53"⟩ ⟨"%51"⟩;
  "%55" ←ₐ .Add ⟨"%54"⟩ ⟨"%46"⟩;
  "%56" ←ₐ .Add ⟨"%55"⟩ ⟨"%44"⟩;
  "%57" ←ₐ .Sub ⟨"%8"⟩ ⟨"%56"⟩;
  "%58" ←ₐ ⟨"%43"⟩ &₀ ⟨"%57"⟩;
  "%59" ←ₐ .Get ⟨"data"⟩ 0 17;
  "%60" ←ₐ .Get ⟨"data"⟩ 0 16;
  "%61" ←ₐ .Mul ⟨"%60"⟩ ⟨"%0"⟩;
  "%62" ←ₐ .Add ⟨"%61"⟩ ⟨"%59"⟩;
  "%63" ←ₐ .Sub ⟨"%7"⟩ ⟨"%62"⟩;
  "%64" ←ₐ ⟨"%58"⟩ &₀ ⟨"%63"⟩
def getReturn (st: State) : Prop :=
  st.constraintsInVar ⟨"%64"⟩
def run (st: State) : Prop :=
  getReturn (full.runProgram st)

end Code

def start_state (input data : BufferAtTime) : State :=
  { buffers := Map.fromList [(⟨"in"⟩, [input]), (⟨"data"⟩, [data])]
  , bufferWidths := Map.fromList [(⟨"in"⟩, 4), (⟨"data"⟩, 18)] --input width 128?
  , constraints := []
  , cycle := 0
  , felts := Map.empty
  , props := Map.empty
  , vars := [⟨"in"⟩, ⟨"data"⟩]
  , isFailed := false
  }

end Risc0.ComputeDecode.Constraints
