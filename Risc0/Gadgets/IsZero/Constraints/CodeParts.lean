import Risc0.Gadgets.IsZero.Constraints.CodeReordered

namespace Risc0.IsZero.Constraints.Code

open MLIRNotation

def part0 : MLIRProgram :=   "%1" ←ₐ ⊤; "%2" ←ₐ .Get ⟨"in"⟩ 0 0; "%4" ←ₐ ⟨"%1"⟩ &₀ ⟨"%2"⟩; "%3" ←ₐ .Get ⟨"data"⟩ 0 0
def part1 : MLIRProgram :=   "%5" ←ₐ guard ⟨"%3"⟩ & ⟨"%1"⟩ with ⟨"%4"⟩; "%0" ←ₐ .Const 1; "%6" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%7" ←ₐ .Get ⟨"data"⟩ 0 1
def part2 : MLIRProgram :=   "%8" ←ₐ .Mul ⟨"%2"⟩ ⟨"%7"⟩; "%9" ←ₐ .Sub ⟨"%8"⟩ ⟨"%0"⟩; "%10" ←ₐ ⟨"%1"⟩ &₀ ⟨"%9"⟩; "%11" ←ₐ guard ⟨"%6"⟩ & ⟨"%5"⟩ with ⟨"%10"⟩

def part0_to_end : MLIRProgram :=   "%1" ←ₐ ⊤; "%2" ←ₐ .Get ⟨"in"⟩ 0 0; "%4" ←ₐ ⟨"%1"⟩ &₀ ⟨"%2"⟩; "%3" ←ₐ .Get ⟨"data"⟩ 0 0; "%5" ←ₐ guard ⟨"%3"⟩ & ⟨"%1"⟩ with ⟨"%4"⟩; "%0" ←ₐ .Const 1; "%6" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%7" ←ₐ .Get ⟨"data"⟩ 0 1; "%8" ←ₐ .Mul ⟨"%2"⟩ ⟨"%7"⟩; "%9" ←ₐ .Sub ⟨"%8"⟩ ⟨"%0"⟩; "%10" ←ₐ ⟨"%1"⟩ &₀ ⟨"%9"⟩; "%11" ←ₐ guard ⟨"%6"⟩ & ⟨"%5"⟩ with ⟨"%10"⟩
def part1_to_end : MLIRProgram :=   "%5" ←ₐ guard ⟨"%3"⟩ & ⟨"%1"⟩ with ⟨"%4"⟩; "%0" ←ₐ .Const 1; "%6" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%7" ←ₐ .Get ⟨"data"⟩ 0 1; "%8" ←ₐ .Mul ⟨"%2"⟩ ⟨"%7"⟩; "%9" ←ₐ .Sub ⟨"%8"⟩ ⟨"%0"⟩; "%10" ←ₐ ⟨"%1"⟩ &₀ ⟨"%9"⟩; "%11" ←ₐ guard ⟨"%6"⟩ & ⟨"%5"⟩ with ⟨"%10"⟩
def part2_to_end : MLIRProgram :=   "%8" ←ₐ .Mul ⟨"%2"⟩ ⟨"%7"⟩; "%9" ←ₐ .Sub ⟨"%8"⟩ ⟨"%0"⟩; "%10" ←ₐ ⟨"%1"⟩ &₀ ⟨"%9"⟩; "%11" ←ₐ guard ⟨"%6"⟩ & ⟨"%5"⟩ with ⟨"%10"⟩

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
end Risc0.IsZero.Constraints.Code