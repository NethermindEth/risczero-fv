import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Is0.Basic

namespace Risc0

section WithMLIR 

variable {α : IsNondet} {st : State} {name : String}

open MLIRNotation
open IsNondet

lemma MLIR.run_assign :
  Γ st ⟦name ←ₐ op⟧ = st[name] := op.eval st := rfl

lemma MLIR.run_Sequence_Assign_collapsible {op : Op α} {program : MLIR α} :
    Γ st ⟦name ←ₐ op; program⟧ = Γ (st[name] := Op.eval st op) ⟦program⟧ := by
  cases op <;> conv => lhs; simp [MLIR.run, State.update, Map.update, beq_iff_eq]

lemma MLIR.run_set : Γ st ⟦MLIR.SetOutput i x⟧ = 
  match st.felts x.name with
    | .some x => {st with output := st.output.set i x}
    | _       => st := rfl

lemma MLIR.run_Sequence_Set_collapsible
    {nameₓ : String}
    {program : MLIR InNondet}
    (x : Felt)
    (h₁ : st.felts nameₓ = some x) :
    Γ st ⟦output[i] ←ᵢ ⟨nameₓ⟩; program⟧ = 
    Γ { st with output := st.output.set i x } ⟦program⟧ := by simp [run, *]

lemma MLIR.run_Set_collapsible
    {nameₓ : String}
    (x : Felt)
    (h₁ : st.felts nameₓ = some x) :
    Γ st ⟦output[i] ←ᵢ ⟨nameₓ⟩⟧ = 
    { st with output := st.output.set i x } := by simp [run, *]

lemma MLIR.run_if_true {c : Variable Felt}
  (h : st.felts c.name = some 0) :
  Γ st ⟦guard c then prog⟧ = st := by
  simp only [run]; generalize eq : st.felts c.name = cond
  rcases cond with _ | ⟨x⟩ <;> simp only
  rw [eq] at h
  cases h
  simp only
  simp only [ite_true]

lemma MLIR.run_if_false {c : Variable Felt}
  (x : Felt)
  (h₁ : st.felts c.name = some x)
  (h₂ : x ≠ 0) :
  Γ st ⟦guard c then prog⟧ = Γ st ⟦prog⟧ := by
  simp only [run]; generalize eq : st.felts c.name = cond
  rcases cond with _ | ⟨y⟩ <;> simp only <;> rw [eq] at h₁
  · cases h₁
  · simp; intros contra
    rw [contra] at h₁
    injection h₁ with contra
    exact absurd contra.symm h₂

lemma MLIR.run_seq :
  Γ st ⟦p₁; p₂⟧ = Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ := rfl

lemma MLIR.run_Sequence_If_collapsible
    {branch : MLIR α}
    {program : MLIR α}
    (x : Felt)
    (h₁ : st.felts name = some x)
    : Γ st ⟦guard ⟨name⟩ then branch; program⟧
  = if (x == 0)
      then Γ st ⟦program⟧
      else Γ st ⟦branch; program⟧ := by
    generalize eq : (x == 0) = cond
    rw [run_seq]
    rcases cond with _ | _ <;> simp only
    · rw [run_if_false x h₁ (by simp at eq; exact eq)]; rfl
    · rw [run_if_true (by simp at eq; rw [eq] at h₁; exact h₁)]; rfl

lemma MLIR.run_If_collapsible
    {branch : MLIR α}
    (x : Felt)
    (h₁ : st.felts name = some x) :
    Γ st ⟦guard ⟨name⟩ then branch⟧
  = if (x == 0)
      then st
      else Γ st ⟦branch⟧ := by simp [run, h₁]

lemma MLIR.run_Sequence_nondet_collapsible :
  Γ st ⟦nondet block; program⟧ = Γ (Γ st ⟦block⟧) ⟦program⟧ := rfl

lemma MLIR.run_Eqz_collapsible
    (x : Felt)
    (h₁ : st.felts name = some x) :
    Γ st ⟦@MLIR.Eqz α ⟨name⟩⟧ 
  = { st with constraints := (x = 0) :: st.constraints } := by simp [run, *]

lemma MLIR.run_Sequence_Eqz_collapsible
    {program : MLIR α}
    (x : Felt)
    (h₁ : st.felts name = some x) :
    Γ st ⟦.Sequence (.Eqz (Variable.mk name)) program⟧
  = let state₁ := { st with constraints := (x = 0) :: st.constraints }
    let state₂ := Γ state₁ ⟦program⟧
    state₂ := by rw [run_seq, run_Eqz_collapsible _ h₁]

end WithMLIR 

end Risc0
