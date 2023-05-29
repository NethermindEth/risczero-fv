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
  match st.felts val.name with
    | .some val => st.set! buf offset val
    | _         => st := rfl

lemma run_seq_def : Γ st ⟦p₁; p₂⟧ = Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ := rfl

lemma run_nondet : Γ st ⟦nondet block⟧ = Γ st ⟦block⟧ := rfl

lemma run_if (x : Felt) (h₁ : st.felts name = some x) :
  Γ st ⟦guard ⟨name⟩ then branch⟧
  = if x = 0 then st else Γ st ⟦branch⟧ := by simp [run, h₁]

lemma run_eqz (x : Felt) (h₁ : st.felts name = some x) :
  Γ st ⟦@MLIR.Eqz α ⟨name⟩⟧ = withEqZero x st := by simp [run, h₁]

end MLIR

end WithMLIR 

end Risc0
