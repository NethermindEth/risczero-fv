-- This file contains the MLIR program labeled `ORIGINAL` in the `nonzero-example` output.
import Mathlib.Data.Vector.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

import Risc0.Cirgen
import Risc0.Lemmas
import Risc0.Gadgets.IsZero.Constraints.Code
import Risc0.Gadgets.IsZero.Constraints.WeakestPresPart2
import Risc0.Gadgets.IsZero.Witness.Code
import Risc0.Gadgets.IsZero.Witness.WeakestPresPart2

namespace Risc0.IsZero

open MLIRNotation

theorem constraints_of_witness
  {input : Felt}
  {output : BufferAtTime}
  (h : output.length = 2) 
  (h₁ : output.all Option.isSome) :
  -- Constraints.Code.run (Witness.Code.run (Witness.WP.start_state input)) := by
  Witness.Code.run (Witness.start_state [input]) (output) → Constraints.Code.run (Constraints.start_state [input] output) := by
  rcases output with _ | ⟨y1, _ | ⟨y₂, ⟨_ | _⟩⟩⟩ <;> try simp at *
  try try simp only [Option.isSome_iff_exists] at h₁
  rcases h₁ with ⟨⟨w₁, h₁⟩, ⟨w₂, h₂⟩⟩; subst h₁ h₂
  rw [Constraints.WP.closed_form, Witness.WP.closed_form]
  repeat split; all_goals try simp [*] at *; try intros; try simp [*] at *
  aesop'

theorem spec_of_constraints {x: Felt} {y₁ y₂: Option Felt}
  (hy₁ : y₁.isSome) (hy₂: y₂.isSome) :
  Constraints.Code.run (Constraints.start_state [x] ([y₁, y₂])) → (
    x = 0 ∧ y₁ = some 1 ∨
    x ≠ 0 ∧ y₁ = some 0 ∧ y₂ = x⁻¹
  ) := by
  try try simp only [Option.isSome_iff_exists] at hy₁
  try try simp only [Option.isSome_iff_exists] at hy₂
  rcases hy₁ with ⟨is0, hy₁_val⟩; subst y₁
  rcases hy₂ with ⟨inv, hy₂_val⟩; subst y₂
  rewrite [Constraints.WP.closed_form]
  try simp
  intro hy₁ hy₂
  try simp [sub_eq_iff_eq_add, *] at *
  rw [←if_true_left] at hy₁ hy₂
  split_ifs at hy₁ hy₂ <;> aesop'
  rw [inv_eq_of_mul_eq_one_right hy₂]

end Risc0.IsZero
