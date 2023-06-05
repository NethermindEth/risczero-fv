import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Is0.Basic

namespace Risc0

section WithMLIR 

variable {α : IsNondet} {st : State} {name : String}

open MLIRNotation IsNondet
open Risc0.VarType

namespace MLIR

lemma run_ass_def : Γ st ⟦name ←ₐ op⟧ = st[name] := Γ st ⟦op⟧ₑ := rfl

lemma run_set_def : Γ st ⟦buf[offset] ←ᵢ val⟧ = 
  match st.felts val with
    | .some val => st.set! buf offset val
    | _         => st := rfl

lemma run_seq_def : Γ st ⟦p₁; p₂⟧ = Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ := rfl

lemma run_nondet : Γ st ⟦nondet block⟧ = Γ st ⟦block⟧ := rfl

-- lemma run_set_output (x : Felt) (h₁ : st.felts nameₓ = some x) :
--   Γ st ⟦⟨"output"⟩[i] ←ᵢ nameₓ⟧ = { st with output := st.output.set i x } := by simp [run_set_def, h₁]
-- TODO run_set_buffer

lemma run_if (x : Felt) (h₁ : st.felts ⟨name⟩  = some x) :
  Γ st ⟦guard ⟨name⟩ then branch⟧
  = if x = 0 then st else Γ st ⟦branch⟧ := by simp [run, h₁]

lemma run_eqz (x : Felt) (h₁ : st.felts ⟨name⟩ = some x) :
  Γ st ⟦@MLIR.Eqz α ⟨name⟩⟧ = withEqZero x st := by simp [run, h₁]

lemma run_composes (program_halves: program = (first_half; second_half)) :
  MLIR.runProgram program start_state = MLIR.runProgram second_half (MLIR.runProgram first_half start_state) := by
  simp [program_halves, run_seq_def]

lemma seq_associative : MLIR.runProgram (p₁; (p₂; p₃)) state = MLIR.runProgram ((p₁; p₂); p₃) state := by
  simp [run_seq_def]

end MLIR

end WithMLIR 

end Risc0
