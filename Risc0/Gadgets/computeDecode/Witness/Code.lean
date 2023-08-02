import Risc0.Lemmas

namespace Risc0.computeDecode.Witness.Code

open MLIRNotation

def full : MLIRProgram :=
  "%0" ←ₐ .Const 64;
  "%1" ←ₐ .Const 8;
  "%2" ←ₐ .Const 16;
  "%3" ←ₐ .Const 0;
  "%4" ←ₐ .Const 128;
  "%5" ←ₐ .Const 4;
  "%6" ←ₐ .Const 3;
  "%7" ←ₐ .Const 2;
  "%8" ←ₐ .Const 1;
  nondet (
    ⟨"data"⟩[10] ←ᵢ ⟨"%3"⟩;
    ⟨"data"⟩[1] ←ᵢ ⟨"%3"⟩;
    ⟨"data"⟩[9] ←ᵢ ⟨"%3"⟩;
    ⟨"data"⟩[8] ←ᵢ ⟨"%3"⟩;
    ⟨"data"⟩[0] ←ᵢ ⟨"%7"⟩;
    ⟨"data"⟩[13] ←ᵢ ⟨"%3"⟩;
    ⟨"data"⟩[12] ←ᵢ ⟨"%3"⟩;
    ⟨"data"⟩[2] ←ᵢ ⟨"%3"⟩;
    ⟨"data"⟩[11] ←ᵢ ⟨"%3"⟩;
    ⟨"data"⟩[4] ←ᵢ ⟨"%3"⟩;
    ⟨"data"⟩[3] ←ᵢ ⟨"%6"⟩;
    ⟨"data"⟩[14] ←ᵢ ⟨"%3"⟩;
    ⟨"data"⟩[15] ←ᵢ ⟨"%3"⟩;
    ⟨"data"⟩[5] ←ᵢ ⟨"%3"⟩;
    ⟨"data"⟩[7] ←ᵢ ⟨"%3"⟩;
    ⟨"data"⟩[6] ←ᵢ ⟨"%7"⟩;
    ⟨"data"⟩[16] ←ᵢ ⟨"%3"⟩;
    ⟨"data"⟩[17] ←ᵢ ⟨"%8"⟩
  );
  "%9" ←ₐ .Get ⟨"data"⟩ 0 13;
  "%10" ←ₐ .Get ⟨"data"⟩ 0 0;
  "%11" ←ₐ .Get ⟨"data"⟩ 0 8;
  "%12" ←ₐ .Mul ⟨"%11"⟩ ⟨"%5"⟩;
  "%13" ←ₐ .Get ⟨"data"⟩ 0 9;
  "%14" ←ₐ .Mul ⟨"%13"⟩ ⟨"%1"⟩;
  "%15" ←ₐ .Get ⟨"data"⟩ 0 1;
  "%16" ←ₐ .Mul ⟨"%15"⟩ ⟨"%2"⟩;
  "%17" ←ₐ .Add ⟨"%16"⟩ ⟨"%14"⟩;
  "%18" ←ₐ .Add ⟨"%17"⟩ ⟨"%12"⟩;
  "%19" ←ₐ .Add ⟨"%18"⟩ ⟨"%10"⟩;
  "%20" ←ₐ .Get ⟨"data"⟩ 0 10;
  "%21" ←ₐ .Mul ⟨"%20"⟩ ⟨"%0"⟩;
  "%22" ←ₐ .Add ⟨"%21"⟩ ⟨"%19"⟩;
  "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%7"⟩;
  "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩;
  "%25" ←ₐ .Sub ⟨"%5"⟩ ⟨"%24"⟩;
  ?₀ ⟨"%25"⟩;
  "%26" ←ₐ .Get ⟨"data"⟩ 0 3;
  "%27" ←ₐ .Get ⟨"data"⟩ 0 4;
  "%28" ←ₐ .Mul ⟨"%27"⟩ ⟨"%5"⟩;
  "%29" ←ₐ .Get ⟨"data"⟩ 0 11;
  "%30" ←ₐ .Get ⟨"data"⟩ 0 2;
  "%31" ←ₐ .Mul ⟨"%30"⟩ ⟨"%7"⟩;
  "%32" ←ₐ .Get ⟨"data"⟩ 0 12;
  "%33" ←ₐ .Mul ⟨"%32"⟩ ⟨"%1"⟩;
  "%34" ←ₐ .Add ⟨"%33"⟩ ⟨"%31"⟩;
  "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%29"⟩;
  "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%2"⟩;
  "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%28"⟩;
  "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%26"⟩;
  "%39" ←ₐ .Sub ⟨"%6"⟩ ⟨"%38"⟩;
  ?₀ ⟨"%39"⟩;
  "%40" ←ₐ .Get ⟨"data"⟩ 0 6;
  "%41" ←ₐ .Get ⟨"data"⟩ 0 7;
  "%42" ←ₐ .Mul ⟨"%41"⟩ ⟨"%5"⟩;
  "%43" ←ₐ .Get ⟨"data"⟩ 0 5;
  "%44" ←ₐ .Get ⟨"data"⟩ 0 15;
  "%45" ←ₐ .Mul ⟨"%44"⟩ ⟨"%5"⟩;
  "%46" ←ₐ .Add ⟨"%45"⟩ ⟨"%43"⟩;
  "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%2"⟩;
  "%48" ←ₐ .Get ⟨"data"⟩ 0 14;
  "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩;
  "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩;
  "%51" ←ₐ .Add ⟨"%50"⟩ ⟨"%42"⟩;
  "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩;
  "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩;
  ?₀ ⟨"%53"⟩;
  "%54" ←ₐ .Get ⟨"data"⟩ 0 17;
  "%55" ←ₐ .Get ⟨"data"⟩ 0 16;
  "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩;
  "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩;
  "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩;
  ?₀ ⟨"%58"⟩
def getReturn (st: State) (res_data: BufferAtTime) : Prop :=
  ((st.buffers ⟨"data"⟩ |>.get!.getLast!) = res_data)
∧ ¬ st.isFailed
def run (st: State) (res_data: BufferAtTime): Prop :=
  getReturn (full.runProgram st) res_data

end Code

def start_state (input_in: BufferAtTime) : State :=
  { buffers := Map.fromList [(⟨"in"⟩, [input_in]), (⟨"data"⟩, [[.none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none]])]
  , felts := Map.empty
  , props := Map.empty
  , isFailed := false
  , bufferWidths := Map.fromList [(⟨"in"⟩, 1), (⟨"data"⟩, 18)]
  , cycle := 0
  , vars := [⟨"in"⟩, ⟨"data"⟩]
  }

end Risc0.computeDecode.Witness
