-- This file contains the MLIR program labeled `ORIGINAL` in the `nonzero-example` output.
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.FieldSimp

import Risc0.Basic
import Risc0.Lemmas
import Risc0.Gadgets.IsZero.Axioms

namespace Risc0

open MLIRNotation

open MLIR in
theorem is0_constraints_if_is0_witness
  {input : Felt}
  {output : List (Option Felt)}
  (h : output.length = 2) 
  (h₁ : output.all Option.isSome) :
  is0_witness_initial input = output → is0_constraints_initial input output := by
  rcases output with _ | ⟨y₁, _ | ⟨y₂, ⟨_ | _⟩⟩⟩ <;> simp at *
  simp only [Option.isSome_iff_exists] at h₁
  rcases h₁ with ⟨⟨w₁, h₁⟩, ⟨w₂, h₂⟩⟩; subst h₁ h₂
  rw [constraints.is0_constraints_closed_form, is0_witness_closed_form]
  repeat split; all_goals simp [*] at *; try intros ; simp [*] at *
  aesop

theorem is0_spec_of_constraints {x} {y₁ y₂ : Option Felt} {state : State}
  (h : y₁.isSome) (h₁ : y₂.isSome) :
  is0_constraints_initial x ([y₁, y₂]) → .some (.Val y₁.get!) = Op.eval {state with felts := Map.empty[⟨"x"⟩] ←ₘ x} (.Isz ⟨"x"⟩) := by
  simp only [Option.isSome_iff_exists] at h h₁
  rcases h with ⟨w, h⟩
  rcases h₁ with ⟨w₁, h₁⟩
  subst h h₁
  rw [constraints.is0_constraints_closed_form]; aesop; aesop
  rw [sub_eq_iff_eq_add] at h; simp [h]; aesop
  simp [Option.get!, Map.update] at h
  subst h
  simp at a

end Risc0
