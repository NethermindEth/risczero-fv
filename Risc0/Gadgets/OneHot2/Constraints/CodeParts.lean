import Risc0.Gadgets.OneHot2.Constraints.CodeReordered

namespace Risc0.OneHot2.Constraints.Code

open MLIRNotation

def part0 : MLIRProgram :=   "%1" ←ₐ ⊤; "%2" ←ₐ .Get ⟨"code"⟩ 0 0; "%3" ←ₐ .Get ⟨"data"⟩ 0 1; "%4" ←ₐ .Sub ⟨"%3"⟩ ⟨"%2"⟩
def part1 : MLIRProgram :=   "%5" ←ₐ ⟨"%1"⟩ &₀ ⟨"%4"⟩; "%0" ←ₐ .Const 1; "%6" ←ₐ .Get ⟨"data"⟩ 0 0; "%7" ←ₐ .Sub ⟨"%0"⟩ ⟨"%6"⟩
def part2 : MLIRProgram :=   "%8" ←ₐ .Mul ⟨"%6"⟩ ⟨"%7"⟩; "%9" ←ₐ ⟨"%5"⟩ &₀ ⟨"%8"⟩; "%10" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%11" ←ₐ .Mul ⟨"%3"⟩ ⟨"%10"⟩
def part3 : MLIRProgram :=   "%12" ←ₐ ⟨"%9"⟩ &₀ ⟨"%11"⟩; "%13" ←ₐ .Add ⟨"%6"⟩ ⟨"%3"⟩; "%14" ←ₐ .Sub ⟨"%13"⟩ ⟨"%0"⟩; "%15" ←ₐ ⟨"%12"⟩ &₀ ⟨"%14"⟩

def part0_to_end : MLIRProgram :=   "%1" ←ₐ ⊤; "%2" ←ₐ .Get ⟨"code"⟩ 0 0; "%3" ←ₐ .Get ⟨"data"⟩ 0 1; "%4" ←ₐ .Sub ⟨"%3"⟩ ⟨"%2"⟩; "%5" ←ₐ ⟨"%1"⟩ &₀ ⟨"%4"⟩; "%0" ←ₐ .Const 1; "%6" ←ₐ .Get ⟨"data"⟩ 0 0; "%7" ←ₐ .Sub ⟨"%0"⟩ ⟨"%6"⟩; "%8" ←ₐ .Mul ⟨"%6"⟩ ⟨"%7"⟩; "%9" ←ₐ ⟨"%5"⟩ &₀ ⟨"%8"⟩; "%10" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%11" ←ₐ .Mul ⟨"%3"⟩ ⟨"%10"⟩; "%12" ←ₐ ⟨"%9"⟩ &₀ ⟨"%11"⟩; "%13" ←ₐ .Add ⟨"%6"⟩ ⟨"%3"⟩; "%14" ←ₐ .Sub ⟨"%13"⟩ ⟨"%0"⟩; "%15" ←ₐ ⟨"%12"⟩ &₀ ⟨"%14"⟩
def part1_to_end : MLIRProgram :=   "%5" ←ₐ ⟨"%1"⟩ &₀ ⟨"%4"⟩; "%0" ←ₐ .Const 1; "%6" ←ₐ .Get ⟨"data"⟩ 0 0; "%7" ←ₐ .Sub ⟨"%0"⟩ ⟨"%6"⟩; "%8" ←ₐ .Mul ⟨"%6"⟩ ⟨"%7"⟩; "%9" ←ₐ ⟨"%5"⟩ &₀ ⟨"%8"⟩; "%10" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%11" ←ₐ .Mul ⟨"%3"⟩ ⟨"%10"⟩; "%12" ←ₐ ⟨"%9"⟩ &₀ ⟨"%11"⟩; "%13" ←ₐ .Add ⟨"%6"⟩ ⟨"%3"⟩; "%14" ←ₐ .Sub ⟨"%13"⟩ ⟨"%0"⟩; "%15" ←ₐ ⟨"%12"⟩ &₀ ⟨"%14"⟩
def part2_to_end : MLIRProgram :=   "%8" ←ₐ .Mul ⟨"%6"⟩ ⟨"%7"⟩; "%9" ←ₐ ⟨"%5"⟩ &₀ ⟨"%8"⟩; "%10" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%11" ←ₐ .Mul ⟨"%3"⟩ ⟨"%10"⟩; "%12" ←ₐ ⟨"%9"⟩ &₀ ⟨"%11"⟩; "%13" ←ₐ .Add ⟨"%6"⟩ ⟨"%3"⟩; "%14" ←ₐ .Sub ⟨"%13"⟩ ⟨"%0"⟩; "%15" ←ₐ ⟨"%12"⟩ &₀ ⟨"%14"⟩
def part3_to_end : MLIRProgram :=   "%12" ←ₐ ⟨"%9"⟩ &₀ ⟨"%11"⟩; "%13" ←ₐ .Add ⟨"%6"⟩ ⟨"%3"⟩; "%14" ←ₐ .Sub ⟨"%13"⟩ ⟨"%0"⟩; "%15" ←ₐ ⟨"%12"⟩ &₀ ⟨"%14"⟩

abbrev parts_combined : MLIRProgram :=
  part0; part1; part2; part3

lemma parts_combine3 :
  Γ st ⟦part3⟧ =
  Γ st ⟦part3_to_end⟧ := by
    rfl
lemma parts_combine2 :
  Γ st ⟦part2; part3⟧ =
  Γ st ⟦part2_to_end⟧ := by
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
    rewrite [parts_combine3]
    rfl
lemma parts_combine1 :
  Γ st ⟦part1; part2; part3⟧ =
  Γ st ⟦part1_to_end⟧ := by
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
    rewrite [parts_combine2]
    rfl
lemma parts_combine0 :
  Γ st ⟦part0; part1; part2; part3⟧ =
  Γ st ⟦part0_to_end⟧ := by
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
    rewrite [parts_combine1]
    rfl
lemma parts_combine :
  Γ st ⟦parts_combined⟧ =
  Γ st ⟦opt_full⟧ := 
    parts_combine0
end Risc0.OneHot2.Constraints.Code