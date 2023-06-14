import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Risc0.Basic

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

lemma run_valid_get {st: State} {name: String} {x y: Option Lit} {back offset : ℕ} 
  (h_cycle: back ≤ st.cycle) (h_vars: ⟨name⟩ ∈ st.vars)
  (h_offset: offset < st.bufferWidths.get! ⟨name⟩)
  (h_value: ((st.buffers.get! ⟨name⟩).get! (st.cycle - Back.toNat back, offset)).isSome = true) :
  (
    st[name] := if
      back ≤ st.cycle ∧
      ⟨name⟩ ∈ st.vars ∧
      offset < st.bufferWidths.get! ⟨name⟩ ∧
      Option.isSome (Buffer.get! (st.buffers.get! ⟨name⟩) (st.cycle - Back.toNat back, offset)) = true
    then x
    else y
  )
  =
  (st[name] := x) := by
  aesop

lemma seq_assoc : Γ state ⟦p₁; (p₂; p₃)⟧ = Γ state ⟦(p₁; p₂); p₃⟧ := by simp [run_seq_def]

end MLIR

end WithMLIR 

end Risc0
