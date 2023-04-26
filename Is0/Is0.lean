-- This file contains the MLIR program labeled `ORIGINAL` in the `nonzero-example` output.
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.FieldSimp

import Is0.Basic
import Is0.Lemmas
import Is0.Programs

namespace Risc0

open MLIRNotation

open MLIR in
theorem is0_constraints_if_is0_witness
  {input output : List Felt}
  (h : input.length = 1 ∧ output.length = 2) :
  (is0_witness input = output → is0_constraints input output) := by
  rcases h with ⟨hin, hout⟩
  rcases input with _ | ⟨x, _ | _⟩ <;> simp only [List.length_cons, List.length_singleton, Nat.succ.injEq, add_eq_zero_iff, and_false, OfNat.one_ne_ofNat] at hin ; clear hin
  rcases output with _ | ⟨y₁, _ | ⟨y₂, ⟨_ | _⟩⟩⟩ <;> simp only [List.length_cons, List.length_singleton, Nat.succ.injEq, add_eq_zero_iff, and_false, OfNat.one_ne_ofNat] at hout ; clear hout
  rw [is0_constraints_closed_form]
  rw [is0_witness_closed_form]
  intros h₁
  by_cases eq : x = 0 <;> simp only [eq]
  · by_cases eq₁ : y₁ = 0 <;> simp only [eq₁]
    subst eq eq₁
    simp only [ite_true, inv_zero, ite_self] at h₁
    simp only [List.set, List.cons.injEq, and_true, false_and] at h₁
    subst eq
    simp only [ite_true, inv_zero, ite_self] at h₁
    simp only [List.set, List.cons.injEq, and_true] at h₁
    rcases h₁ with ⟨h₁, h₂⟩
    subst h₁ h₂
    simp only
  · by_cases eq₁ : y₁ = 0 <;> simp only [eq₁, sub_zero, one_ne_zero, ite_true, true_and, ite_false]
    · subst eq₁
      simp only [List.set, List.cons.injEq, ite_eq_right_iff, and_true] at h₁
      rw [←h₁.2]
      simp only [eq, ite_false, ne_eq, not_false_iff, mul_inv_cancel, sub_self]
    · simp only [List.set, eq, ite_false, List.cons.injEq, and_true] at h₁
      tauto

theorem pseudocompleteness {x y₁ y₂ : Felt} {state : State} :
  is0_constraints [x] [y₁, y₂] → .Val y₂ = Op.eval {state with felts := Map.empty["x"] := x} (.Isz ⟨"x"⟩) := by sorry

end Risc0
