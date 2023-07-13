import Risc0.Gadgets.OneHot1.Witness.CodeReordered

namespace Risc0.OneHot1.Witness.Code

open MLIRNotation

def part0 : MLIRProgram :=   "%2" ←ₐ .Get ⟨"code"⟩ 0 0; nondet ( "%8" ←ₐ ??₀⟨"%2"⟩; ⟨"data"⟩[0] ←ᵢ ⟨"%8"⟩ ); "%1" ←ₐ .Const 0
def part1 : MLIRProgram :=   "%3" ←ₐ .Sub ⟨"%1"⟩ ⟨"%2"⟩; ?₀ ⟨"%3"⟩; "%0" ←ₐ .Const 1; "%4" ←ₐ .Get ⟨"data"⟩ 0 0
def part2 : MLIRProgram :=   "%5" ←ₐ .Sub ⟨"%0"⟩ ⟨"%4"⟩; "%6" ←ₐ .Mul ⟨"%4"⟩ ⟨"%5"⟩; ?₀ ⟨"%6"⟩; "%7" ←ₐ .Sub ⟨"%4"⟩ ⟨"%0"⟩
def part3 : MLIRProgram :=   ?₀ ⟨"%7"⟩

def part0_to_end : MLIRProgram :=   "%2" ←ₐ .Get ⟨"code"⟩ 0 0; nondet ( "%8" ←ₐ ??₀⟨"%2"⟩; ⟨"data"⟩[0] ←ᵢ ⟨"%8"⟩ ); "%1" ←ₐ .Const 0; "%3" ←ₐ .Sub ⟨"%1"⟩ ⟨"%2"⟩; ?₀ ⟨"%3"⟩; "%0" ←ₐ .Const 1; "%4" ←ₐ .Get ⟨"data"⟩ 0 0; "%5" ←ₐ .Sub ⟨"%0"⟩ ⟨"%4"⟩; "%6" ←ₐ .Mul ⟨"%4"⟩ ⟨"%5"⟩; ?₀ ⟨"%6"⟩; "%7" ←ₐ .Sub ⟨"%4"⟩ ⟨"%0"⟩; ?₀ ⟨"%7"⟩
def part1_to_end : MLIRProgram :=   "%3" ←ₐ .Sub ⟨"%1"⟩ ⟨"%2"⟩; ?₀ ⟨"%3"⟩; "%0" ←ₐ .Const 1; "%4" ←ₐ .Get ⟨"data"⟩ 0 0; "%5" ←ₐ .Sub ⟨"%0"⟩ ⟨"%4"⟩; "%6" ←ₐ .Mul ⟨"%4"⟩ ⟨"%5"⟩; ?₀ ⟨"%6"⟩; "%7" ←ₐ .Sub ⟨"%4"⟩ ⟨"%0"⟩; ?₀ ⟨"%7"⟩
def part2_to_end : MLIRProgram :=   "%5" ←ₐ .Sub ⟨"%0"⟩ ⟨"%4"⟩; "%6" ←ₐ .Mul ⟨"%4"⟩ ⟨"%5"⟩; ?₀ ⟨"%6"⟩; "%7" ←ₐ .Sub ⟨"%4"⟩ ⟨"%0"⟩; ?₀ ⟨"%7"⟩
def part3_to_end : MLIRProgram :=   ?₀ ⟨"%7"⟩

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
    rewrite [MLIR.part_assoc_dnnd]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.nondet_step_eq
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
end Risc0.OneHot1.Witness.Code