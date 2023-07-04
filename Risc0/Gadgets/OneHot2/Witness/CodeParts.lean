import Risc0.Gadgets.OneHot2.Witness.CodeReordered

namespace Risc0.OneHot2.Witness.Code

open MLIRNotation

def part0 : MLIRProgram :=   "%2" ←ₐ .Get ⟨"code"⟩ 0 0; nondet ( "%12" ←ₐ ??₀⟨"%2"⟩; ⟨"data"⟩[0] ←ᵢ ⟨"%12"⟩ ); "%0" ←ₐ .Const 1
def part1 : MLIRProgram :=   nondet ( "%13" ←ₐ .Sub ⟨"%2"⟩ ⟨"%0"⟩; "%14" ←ₐ ??₀⟨"%13"⟩; ⟨"data"⟩[1] ←ᵢ ⟨"%14"⟩ ); "%3" ←ₐ .Get ⟨"data"⟩ 0 1
def part2 : MLIRProgram :=   "%4" ←ₐ .Sub ⟨"%3"⟩ ⟨"%2"⟩; ?₀ ⟨"%4"⟩; "%5" ←ₐ .Get ⟨"data"⟩ 0 0; "%6" ←ₐ .Sub ⟨"%0"⟩ ⟨"%5"⟩
def part3 : MLIRProgram :=   "%7" ←ₐ .Mul ⟨"%5"⟩ ⟨"%6"⟩; ?₀ ⟨"%7"⟩; "%8" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%9" ←ₐ .Mul ⟨"%3"⟩ ⟨"%8"⟩
def part4 : MLIRProgram :=   ?₀ ⟨"%9"⟩; "%10" ←ₐ .Add ⟨"%5"⟩ ⟨"%3"⟩; "%11" ←ₐ .Sub ⟨"%10"⟩ ⟨"%0"⟩; "%1" ←ₐ .Const 0
def part5 : MLIRProgram :=   ?₀ ⟨"%11"⟩

def part0_to_end : MLIRProgram :=   "%2" ←ₐ .Get ⟨"code"⟩ 0 0; nondet ( "%12" ←ₐ ??₀⟨"%2"⟩; ⟨"data"⟩[0] ←ᵢ ⟨"%12"⟩ ); "%0" ←ₐ .Const 1; nondet ( "%13" ←ₐ .Sub ⟨"%2"⟩ ⟨"%0"⟩; "%14" ←ₐ ??₀⟨"%13"⟩; ⟨"data"⟩[1] ←ᵢ ⟨"%14"⟩ ); "%3" ←ₐ .Get ⟨"data"⟩ 0 1; "%4" ←ₐ .Sub ⟨"%3"⟩ ⟨"%2"⟩; ?₀ ⟨"%4"⟩; "%5" ←ₐ .Get ⟨"data"⟩ 0 0; "%6" ←ₐ .Sub ⟨"%0"⟩ ⟨"%5"⟩; "%7" ←ₐ .Mul ⟨"%5"⟩ ⟨"%6"⟩; ?₀ ⟨"%7"⟩; "%8" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%9" ←ₐ .Mul ⟨"%3"⟩ ⟨"%8"⟩; ?₀ ⟨"%9"⟩; "%10" ←ₐ .Add ⟨"%5"⟩ ⟨"%3"⟩; "%11" ←ₐ .Sub ⟨"%10"⟩ ⟨"%0"⟩; "%1" ←ₐ .Const 0; ?₀ ⟨"%11"⟩
def part1_to_end : MLIRProgram :=   nondet ( "%13" ←ₐ .Sub ⟨"%2"⟩ ⟨"%0"⟩; "%14" ←ₐ ??₀⟨"%13"⟩; ⟨"data"⟩[1] ←ᵢ ⟨"%14"⟩ ); "%3" ←ₐ .Get ⟨"data"⟩ 0 1; "%4" ←ₐ .Sub ⟨"%3"⟩ ⟨"%2"⟩; ?₀ ⟨"%4"⟩; "%5" ←ₐ .Get ⟨"data"⟩ 0 0; "%6" ←ₐ .Sub ⟨"%0"⟩ ⟨"%5"⟩; "%7" ←ₐ .Mul ⟨"%5"⟩ ⟨"%6"⟩; ?₀ ⟨"%7"⟩; "%8" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%9" ←ₐ .Mul ⟨"%3"⟩ ⟨"%8"⟩; ?₀ ⟨"%9"⟩; "%10" ←ₐ .Add ⟨"%5"⟩ ⟨"%3"⟩; "%11" ←ₐ .Sub ⟨"%10"⟩ ⟨"%0"⟩; "%1" ←ₐ .Const 0; ?₀ ⟨"%11"⟩
def part2_to_end : MLIRProgram :=   "%4" ←ₐ .Sub ⟨"%3"⟩ ⟨"%2"⟩; ?₀ ⟨"%4"⟩; "%5" ←ₐ .Get ⟨"data"⟩ 0 0; "%6" ←ₐ .Sub ⟨"%0"⟩ ⟨"%5"⟩; "%7" ←ₐ .Mul ⟨"%5"⟩ ⟨"%6"⟩; ?₀ ⟨"%7"⟩; "%8" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%9" ←ₐ .Mul ⟨"%3"⟩ ⟨"%8"⟩; ?₀ ⟨"%9"⟩; "%10" ←ₐ .Add ⟨"%5"⟩ ⟨"%3"⟩; "%11" ←ₐ .Sub ⟨"%10"⟩ ⟨"%0"⟩; "%1" ←ₐ .Const 0; ?₀ ⟨"%11"⟩
def part3_to_end : MLIRProgram :=   "%7" ←ₐ .Mul ⟨"%5"⟩ ⟨"%6"⟩; ?₀ ⟨"%7"⟩; "%8" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%9" ←ₐ .Mul ⟨"%3"⟩ ⟨"%8"⟩; ?₀ ⟨"%9"⟩; "%10" ←ₐ .Add ⟨"%5"⟩ ⟨"%3"⟩; "%11" ←ₐ .Sub ⟨"%10"⟩ ⟨"%0"⟩; "%1" ←ₐ .Const 0; ?₀ ⟨"%11"⟩
def part4_to_end : MLIRProgram :=   ?₀ ⟨"%9"⟩; "%10" ←ₐ .Add ⟨"%5"⟩ ⟨"%3"⟩; "%11" ←ₐ .Sub ⟨"%10"⟩ ⟨"%0"⟩; "%1" ←ₐ .Const 0; ?₀ ⟨"%11"⟩
def part5_to_end : MLIRProgram :=   ?₀ ⟨"%11"⟩

abbrev parts_combined : MLIRProgram :=
  part0; part1; part2; part3; part4; part5

lemma parts_combine5 :
  Γ st ⟦part5⟧ =
  Γ st ⟦part5_to_end⟧ := by
    rfl
lemma parts_combine4 :
  Γ st ⟦part4; part5⟧ =
  Γ st ⟦part4_to_end⟧ := by
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
    rewrite [parts_combine5]
    rfl
lemma parts_combine3 :
  Γ st ⟦part3; part4; part5⟧ =
  Γ st ⟦part3_to_end⟧ := by
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
    rewrite [parts_combine4]
    rfl
lemma parts_combine2 :
  Γ st ⟦part2; part3; part4; part5⟧ =
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
  Γ st ⟦part1; part2; part3; part4; part5⟧ =
  Γ st ⟦part1_to_end⟧ := by
    unfold part1
    rewrite [MLIR.part_assoc_nnnd]
    apply MLIR.nondet_step_eq
    intro st
    apply MLIR.nondet_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine2]
    rfl
lemma parts_combine0 :
  Γ st ⟦part0; part1; part2; part3; part4; part5⟧ =
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
end Risc0.OneHot2.Witness.Code