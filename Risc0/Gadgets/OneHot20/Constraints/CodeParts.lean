import Risc0.Gadgets.OneHot20.Constraints.CodeReordered

namespace Risc0.OneHot20.Constraints.Code

open MLIRNotation

def part0 : MLIRProgram :=   "%6" ←ₐ ⊤; "%4" ←ₐ .Const 4; "%13" ←ₐ .Get ⟨"data"⟩ 0 8; "%14" ←ₐ .Mul ⟨"%13"⟩ ⟨"%4"⟩
def part1 : MLIRProgram :=   "%2" ←ₐ .Const 8; "%15" ←ₐ .Get ⟨"data"⟩ 0 9; "%16" ←ₐ .Mul ⟨"%15"⟩ ⟨"%2"⟩; "%1" ←ₐ .Const 16
def part2 : MLIRProgram :=   "%17" ←ₐ .Get ⟨"data"⟩ 0 1; "%18" ←ₐ .Mul ⟨"%17"⟩ ⟨"%1"⟩; "%19" ←ₐ .Add ⟨"%18"⟩ ⟨"%16"⟩; "%20" ←ₐ .Add ⟨"%19"⟩ ⟨"%14"⟩
def part3 : MLIRProgram :=   "%12" ←ₐ .Get ⟨"data"⟩ 0 0; "%21" ←ₐ .Add ⟨"%20"⟩ ⟨"%12"⟩; "%5" ←ₐ .Const 64; "%22" ←ₐ .Get ⟨"data"⟩ 0 10
def part4 : MLIRProgram :=   "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%5"⟩; "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%21"⟩; "%3" ←ₐ .Const 2; "%25" ←ₐ .Mul ⟨"%24"⟩ ⟨"%3"⟩
def part5 : MLIRProgram :=   "%11" ←ₐ .Get ⟨"data"⟩ 0 13; "%26" ←ₐ .Add ⟨"%25"⟩ ⟨"%11"⟩; "%10" ←ₐ .Get ⟨"in"⟩ 0 3; "%27" ←ₐ .Sub ⟨"%10"⟩ ⟨"%26"⟩
def part6 : MLIRProgram :=   "%28" ←ₐ ⟨"%6"⟩ &₀ ⟨"%27"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 4; "%31" ←ₐ .Mul ⟨"%30"⟩ ⟨"%4"⟩; "%33" ←ₐ .Get ⟨"data"⟩ 0 2
def part7 : MLIRProgram :=   "%34" ←ₐ .Mul ⟨"%33"⟩ ⟨"%3"⟩; "%35" ←ₐ .Get ⟨"data"⟩ 0 12; "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%2"⟩; "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%34"⟩
def part8 : MLIRProgram :=   "%32" ←ₐ .Get ⟨"data"⟩ 0 11; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%32"⟩; "%39" ←ₐ .Mul ⟨"%38"⟩ ⟨"%1"⟩; "%40" ←ₐ .Add ⟨"%39"⟩ ⟨"%31"⟩
def part9 : MLIRProgram :=   "%29" ←ₐ .Get ⟨"data"⟩ 0 3; "%41" ←ₐ .Add ⟨"%40"⟩ ⟨"%29"⟩; "%9" ←ₐ .Get ⟨"in"⟩ 0 2; "%42" ←ₐ .Sub ⟨"%9"⟩ ⟨"%41"⟩
def part10 : MLIRProgram :=   "%43" ←ₐ ⟨"%28"⟩ &₀ ⟨"%42"⟩; "%45" ←ₐ .Get ⟨"data"⟩ 0 7; "%46" ←ₐ .Mul ⟨"%45"⟩ ⟨"%4"⟩; "%48" ←ₐ .Get ⟨"data"⟩ 0 15
def part11 : MLIRProgram :=   "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩; "%47" ←ₐ .Get ⟨"data"⟩ 0 5; "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩; "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%1"⟩
def part12 : MLIRProgram :=   "%0" ←ₐ .Const 128; "%52" ←ₐ .Get ⟨"data"⟩ 0 14; "%53" ←ₐ .Mul ⟨"%52"⟩ ⟨"%0"⟩; "%54" ←ₐ .Add ⟨"%53"⟩ ⟨"%51"⟩
def part13 : MLIRProgram :=   "%55" ←ₐ .Add ⟨"%54"⟩ ⟨"%46"⟩; "%44" ←ₐ .Get ⟨"data"⟩ 0 6; "%56" ←ₐ .Add ⟨"%55"⟩ ⟨"%44"⟩; "%8" ←ₐ .Get ⟨"in"⟩ 0 1
def part14 : MLIRProgram :=   "%57" ←ₐ .Sub ⟨"%8"⟩ ⟨"%56"⟩; "%58" ←ₐ ⟨"%43"⟩ &₀ ⟨"%57"⟩; "%60" ←ₐ .Get ⟨"data"⟩ 0 16; "%61" ←ₐ .Mul ⟨"%60"⟩ ⟨"%0"⟩
def part15 : MLIRProgram :=   "%59" ←ₐ .Get ⟨"data"⟩ 0 17; "%62" ←ₐ .Add ⟨"%61"⟩ ⟨"%59"⟩; "%7" ←ₐ .Get ⟨"in"⟩ 0 0; "%63" ←ₐ .Sub ⟨"%7"⟩ ⟨"%62"⟩
def part16 : MLIRProgram :=   "%64" ←ₐ ⟨"%58"⟩ &₀ ⟨"%63"⟩

abbrev parts_combined : MLIRProgram :=
  part0; part1; part2; part3; part4; part5; part6; part7; part8; part9; part10; part11; part12; part13; part14; part15; part16
lemma parts_combine {st: State} :
  Γ st ⟦parts_combined⟧ =
  Γ st ⟦opt_full⟧ := by
  unfold opt_full parts_combined
  unfold part0
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part1
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part2
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part3
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part4
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part5
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part6
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part7
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part8
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part9
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part10
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part11
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part12
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part13
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part14
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part15
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part16
  rfl
end Risc0.OneHot20.Constraints.Code