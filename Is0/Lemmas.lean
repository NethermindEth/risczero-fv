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

-- MLIR.run def lemmas
lemma MLIR.run_ass_def : Γ st ⟦name ←ₐ op⟧ = st[name] := Γ st ⟦op⟧ₑ := rfl

lemma MLIR.run_set_def : Γ st ⟦output[i] ←ᵢ x⟧ = 
  match st.felts x.name with
    | .some x => {st with output := st.output.set i x}
    | _       => st := rfl

lemma MLIR.run_seq_def : Γ st ⟦p₁; p₂⟧ = Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ := rfl

lemma MLIR.run_nondet : Γ st ⟦nondet block⟧ = Γ st ⟦block⟧ := rfl

lemma MLIR.run_set (x : Felt) (h₁ : st.felts nameₓ = some x) :
  Γ st ⟦output[i] ←ᵢ ⟨nameₓ⟩⟧ = { st with output := st.output.set i x } := by simp [run_set_def, h₁]

lemma MLIR.run_if (x : Felt) (h₁ : st.felts name = some x) :
  Γ st ⟦guard ⟨name⟩ then branch⟧
  = if x = 0 then st else Γ st ⟦branch⟧ := by simp [run, h₁]

lemma MLIR.run_eqz (x : Felt) (h₁ : st.felts name = some x) :
  Γ st ⟦@MLIR.Eqz α ⟨name⟩⟧ = withEqZero x st := by simp [run, h₁]

end WithMLIR 

end Risc0
