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
  rcases input with _ | ⟨x, _ | _⟩ <;> simp at *
  rcases output with _ | ⟨y₁, _ | ⟨y₂, ⟨_ | _⟩⟩⟩ <;> simp at *
  rw [is0_constraints_closed_form, is0_witness_closed_form]
  repeat split; all_goals simp [*] at *; try intros ; simp [*] at *
  aesop

theorem pseudocompleteness {x y₁ y₂ : Felt} {state : State} :
  is0_constraints [x] [y₁, y₂] → .Val y₁ = Op.eval {state with felts := Map.empty["x"] := x} (.Isz ⟨"x"⟩) := by
  rw [is0_constraints_closed_form]; aesop; aesop
  rw [sub_eq_iff_eq_add] at h; simp [h]

end Risc0
