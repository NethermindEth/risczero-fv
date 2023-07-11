import Risc0.Gadgets.IsZero.Witness.CodeReordered

namespace Risc0.IsZero.Witness.Code

open MLIRNotation

def part0 : MLIRProgram :=   "%1" ←ₐ .Get ⟨"in"⟩ 0 0; nondet ( "%4" ←ₐ ??₀⟨"%1"⟩; ⟨"data"⟩[0] ←ᵢ ⟨"%4"⟩; "%5" ←ₐ Inv⟨"%1"⟩ )
def part1 : MLIRProgram :=   nondet ( ⟨"data"⟩[1] ←ᵢ ⟨"%5"⟩ ); "%2" ←ₐ .Get ⟨"data"⟩ 0 0; guard ⟨"%2"⟩ then (?₀ ⟨"%1"⟩); "%0" ←ₐ .Const 1
def part2 : MLIRProgram :=   "%3" ←ₐ .Sub ⟨"%0"⟩ ⟨"%2"⟩; guard ⟨"%3"⟩ then ("%4" ←ₐ .Get ⟨"data"⟩ 0 1; "%5" ←ₐ .Mul ⟨"%1"⟩ ⟨"%4"⟩; "%6" ←ₐ .Sub ⟨"%5"⟩ ⟨"%0"⟩; ?₀ ⟨"%6"⟩)

def part0_to_end : MLIRProgram :=   "%1" ←ₐ .Get ⟨"in"⟩ 0 0; nondet ( "%4" ←ₐ ??₀⟨"%1"⟩; ⟨"data"⟩[0] ←ᵢ ⟨"%4"⟩; "%5" ←ₐ Inv⟨"%1"⟩; ⟨"data"⟩[1] ←ᵢ ⟨"%5"⟩ ); "%2" ←ₐ .Get ⟨"data"⟩ 0 0; guard ⟨"%2"⟩ then (?₀ ⟨"%1"⟩); "%0" ←ₐ .Const 1; "%3" ←ₐ .Sub ⟨"%0"⟩ ⟨"%2"⟩; guard ⟨"%3"⟩ then ("%4" ←ₐ .Get ⟨"data"⟩ 0 1; "%5" ←ₐ .Mul ⟨"%1"⟩ ⟨"%4"⟩; "%6" ←ₐ .Sub ⟨"%5"⟩ ⟨"%0"⟩; ?₀ ⟨"%6"⟩)
def part1_to_end : MLIRProgram :=   nondet ( ⟨"data"⟩[1] ←ᵢ ⟨"%5"⟩ ); "%2" ←ₐ .Get ⟨"data"⟩ 0 0; guard ⟨"%2"⟩ then (?₀ ⟨"%1"⟩); "%0" ←ₐ .Const 1; "%3" ←ₐ .Sub ⟨"%0"⟩ ⟨"%2"⟩; guard ⟨"%3"⟩ then ("%4" ←ₐ .Get ⟨"data"⟩ 0 1; "%5" ←ₐ .Mul ⟨"%1"⟩ ⟨"%4"⟩; "%6" ←ₐ .Sub ⟨"%5"⟩ ⟨"%0"⟩; ?₀ ⟨"%6"⟩)
def part2_to_end : MLIRProgram :=   "%3" ←ₐ .Sub ⟨"%0"⟩ ⟨"%2"⟩; guard ⟨"%3"⟩ then ("%4" ←ₐ .Get ⟨"data"⟩ 0 1; "%5" ←ₐ .Mul ⟨"%1"⟩ ⟨"%4"⟩; "%6" ←ₐ .Sub ⟨"%5"⟩ ⟨"%0"⟩; ?₀ ⟨"%6"⟩)

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
    rewrite [MLIR.part_assoc_nddd]
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
    rewrite [MLIR.part_assoc_dnnn]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.nondet_step_eq
    intro st
    apply MLIR.nondet_step_eq
    intro st
    apply MLIR.nondet_step_eq
    intro st
    rewrite [parts_combine1]
    rfl
lemma parts_combine :
  Γ st ⟦parts_combined⟧ =
  Γ st ⟦opt_full⟧ := 
    parts_combine0
end Risc0.IsZero.Witness.Code