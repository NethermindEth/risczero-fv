import Risc0.Lemmas

namespace Risc0.computeDecode.Constraints.Code

open MLIRNotation

def full : MLIRProgram :=
  "%0" ←ₐ .Const 1;
  "%1" ←ₐ .Const 2;
  "%2" ←ₐ .Const 3;
  "%3" ←ₐ .Const 4;
  "%4" ←ₐ .Const 128;
  "%5" ←ₐ .Const 16;
  "%6" ←ₐ .Const 8;
  "%7" ←ₐ .Const 64;
  "%8" ←ₐ ⊤;
  "%9" ←ₐ .Get ⟨"data"⟩ 0 13;
  "%10" ←ₐ .Get ⟨"data"⟩ 0 0;
  "%11" ←ₐ .Get ⟨"data"⟩ 0 8;
  "%12" ←ₐ .Mul ⟨"%11"⟩ ⟨"%3"⟩;
  "%13" ←ₐ .Get ⟨"data"⟩ 0 9;
  "%14" ←ₐ .Mul ⟨"%13"⟩ ⟨"%6"⟩;
  "%15" ←ₐ .Get ⟨"data"⟩ 0 1;
  "%16" ←ₐ .Mul ⟨"%15"⟩ ⟨"%5"⟩;
  "%17" ←ₐ .Add ⟨"%16"⟩ ⟨"%14"⟩;
  "%18" ←ₐ .Add ⟨"%17"⟩ ⟨"%12"⟩;
  "%19" ←ₐ .Add ⟨"%18"⟩ ⟨"%10"⟩;
  "%20" ←ₐ .Get ⟨"data"⟩ 0 10;
  "%21" ←ₐ .Mul ⟨"%20"⟩ ⟨"%7"⟩;
  "%22" ←ₐ .Add ⟨"%21"⟩ ⟨"%19"⟩;
  "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%1"⟩;
  "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩;
  "%25" ←ₐ .Sub ⟨"%3"⟩ ⟨"%24"⟩;
  "%26" ←ₐ ⟨"%8"⟩ &₀ ⟨"%25"⟩;
  "%27" ←ₐ .Get ⟨"data"⟩ 0 3;
  "%28" ←ₐ .Get ⟨"data"⟩ 0 4;
  "%29" ←ₐ .Mul ⟨"%28"⟩ ⟨"%3"⟩;
  "%30" ←ₐ .Get ⟨"data"⟩ 0 11;
  "%31" ←ₐ .Get ⟨"data"⟩ 0 2;
  "%32" ←ₐ .Mul ⟨"%31"⟩ ⟨"%1"⟩;
  "%33" ←ₐ .Get ⟨"data"⟩ 0 12;
  "%34" ←ₐ .Mul ⟨"%33"⟩ ⟨"%6"⟩;
  "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%32"⟩;
  "%36" ←ₐ .Add ⟨"%35"⟩ ⟨"%30"⟩;
  "%37" ←ₐ .Mul ⟨"%36"⟩ ⟨"%5"⟩;
  "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%29"⟩;
  "%39" ←ₐ .Add ⟨"%38"⟩ ⟨"%27"⟩;
  "%40" ←ₐ .Sub ⟨"%2"⟩ ⟨"%39"⟩;
  "%41" ←ₐ ⟨"%26"⟩ &₀ ⟨"%40"⟩;
  "%42" ←ₐ .Get ⟨"data"⟩ 0 6;
  "%43" ←ₐ .Get ⟨"data"⟩ 0 7;
  "%44" ←ₐ .Mul ⟨"%43"⟩ ⟨"%3"⟩;
  "%45" ←ₐ .Get ⟨"data"⟩ 0 5;
  "%46" ←ₐ .Get ⟨"data"⟩ 0 15;
  "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%3"⟩;
  "%48" ←ₐ .Add ⟨"%47"⟩ ⟨"%45"⟩;
  "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%5"⟩;
  "%50" ←ₐ .Get ⟨"data"⟩ 0 14;
  "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%4"⟩;
  "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%49"⟩;
  "%53" ←ₐ .Add ⟨"%52"⟩ ⟨"%44"⟩;
  "%54" ←ₐ .Add ⟨"%53"⟩ ⟨"%42"⟩;
  "%55" ←ₐ .Sub ⟨"%1"⟩ ⟨"%54"⟩;
  "%56" ←ₐ ⟨"%41"⟩ &₀ ⟨"%55"⟩;
  "%57" ←ₐ .Get ⟨"data"⟩ 0 17;
  "%58" ←ₐ .Get ⟨"data"⟩ 0 16;
  "%59" ←ₐ .Mul ⟨"%58"⟩ ⟨"%4"⟩;
  "%60" ←ₐ .Add ⟨"%59"⟩ ⟨"%57"⟩;
  "%61" ←ₐ .Sub ⟨"%0"⟩ ⟨"%60"⟩;
  "%62" ←ₐ ⟨"%56"⟩ &₀ ⟨"%61"⟩
def getReturn (st: State) : Prop :=
  st.constraintsInVar ⟨"%62"⟩
def run (st: State) : Prop :=
  getReturn (full.runProgram st)

end Code

def start_state (input_in output_data: BufferAtTime) : State :=
  { buffers := Map.fromList [(⟨"in"⟩, [input_in]), (⟨"data"⟩, [output_data])]
  , felts := Map.empty
  , props := Map.empty
  , isFailed := false
  , bufferWidths := Map.fromList [(⟨"in"⟩, 1), (⟨"data"⟩, 18)]
  , cycle := 0
  , vars := [⟨"in"⟩, ⟨"data"⟩]
  }

end Risc0.computeDecode.Constraints
