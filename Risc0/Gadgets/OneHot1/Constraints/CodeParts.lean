import Risc0.Gadgets.OneHot1.Constraints.CodeReordered

namespace Risc0.OneHot1.Constraints.Code

open MLIRNotation

def part0 : MLIRProgram :=   "%2" ←ₐ ⊤; "%0" ←ₐ .Const 0; "%3" ←ₐ .Get ⟨"code"⟩ 0 0; "%4" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩
def part1 : MLIRProgram :=   "%5" ←ₐ ⟨"%2"⟩ &₀ ⟨"%4"⟩; "%1" ←ₐ .Const 1; "%6" ←ₐ .Get ⟨"data"⟩ 0 0; "%7" ←ₐ .Sub ⟨"%1"⟩ ⟨"%6"⟩
def part2 : MLIRProgram :=   "%8" ←ₐ .Mul ⟨"%6"⟩ ⟨"%7"⟩; "%9" ←ₐ ⟨"%5"⟩ &₀ ⟨"%8"⟩; "%10" ←ₐ .Sub ⟨"%6"⟩ ⟨"%1"⟩; "%11" ←ₐ ⟨"%9"⟩ &₀ ⟨"%10"⟩

def part0_to_end : MLIRProgram :=   "%2" ←ₐ ⊤; "%0" ←ₐ .Const 0; "%3" ←ₐ .Get ⟨"code"⟩ 0 0; "%4" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%5" ←ₐ ⟨"%2"⟩ &₀ ⟨"%4"⟩; "%1" ←ₐ .Const 1; "%6" ←ₐ .Get ⟨"data"⟩ 0 0; "%7" ←ₐ .Sub ⟨"%1"⟩ ⟨"%6"⟩; "%8" ←ₐ .Mul ⟨"%6"⟩ ⟨"%7"⟩; "%9" ←ₐ ⟨"%5"⟩ &₀ ⟨"%8"⟩; "%10" ←ₐ .Sub ⟨"%6"⟩ ⟨"%1"⟩; "%11" ←ₐ ⟨"%9"⟩ &₀ ⟨"%10"⟩
def part1_to_end : MLIRProgram :=   "%5" ←ₐ ⟨"%2"⟩ &₀ ⟨"%4"⟩; "%1" ←ₐ .Const 1; "%6" ←ₐ .Get ⟨"data"⟩ 0 0; "%7" ←ₐ .Sub ⟨"%1"⟩ ⟨"%6"⟩; "%8" ←ₐ .Mul ⟨"%6"⟩ ⟨"%7"⟩; "%9" ←ₐ ⟨"%5"⟩ &₀ ⟨"%8"⟩; "%10" ←ₐ .Sub ⟨"%6"⟩ ⟨"%1"⟩; "%11" ←ₐ ⟨"%9"⟩ &₀ ⟨"%10"⟩
def part2_to_end : MLIRProgram :=   "%8" ←ₐ .Mul ⟨"%6"⟩ ⟨"%7"⟩; "%9" ←ₐ ⟨"%5"⟩ &₀ ⟨"%8"⟩; "%10" ←ₐ .Sub ⟨"%6"⟩ ⟨"%1"⟩; "%11" ←ₐ ⟨"%9"⟩ &₀ ⟨"%10"⟩

abbrev parts_combined : MLIRProgram :=
  part0; part1; part2

lemma parts_combine2 :
  Γ st ⟦part2⟧ =
  Γ st ⟦part2_to_end⟧ := by
    rfl
lemma parts_combine1 :
  Γ st ⟦part1; part2⟧ =
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
  Γ st ⟦part0; part1; part2⟧ =
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
end Risc0.OneHot1.Constraints.Code