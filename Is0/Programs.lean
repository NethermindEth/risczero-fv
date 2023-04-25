-- This file contains the MLIR program labeled `ORIGINAL` in the `nonzero-example` output.
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Is0.Basic
import Is0.Lemmas

namespace Risc0

open MLIRNotation in
def is0_witness (input : List Felt) : List Felt :=
  let state' :=
    MLIR.run { felts := Map.empty
             , props := Map.empty
             , input := input
             , output := [42, 42]
             , constraints := []
             } <|
    "x"         ←ₐ input[0];
    "isZeroBit" ←ₐ ??₀⟨"x"⟩;
    output[0]   ←ₐ ⟨"isZeroBit"⟩;
    "invVal"    ←ₐ Inv ⟨"x"⟩;
    output[1]   ←ₐ ⟨"invVal"⟩
  state'.output

open MLIRNotation in
def is0_constraints (input : List Felt) (output : List Felt) : Prop :=
  let state' :=
    MLIR.run { felts := Map.empty
             , props := Map.empty
             , input := input
             , output := output
             , constraints := []
             } <|
    "1"         ←ₐ 1;
    "x"         ←ₐ input[0];
    "out[0]"    ←ₐ output[0];
    guard ⟨"out[0]"⟩ then
      ?₀⟨"x"⟩;
    "1 - out[0]" ←ₐ ⟨"1"⟩ - ⟨"out[0]"⟩;
    guard ⟨"1 - out[0]"⟩ then (
      "out[1]"         ←ₐ output[1];
      "x * out[1]"     ←ₐ ⟨"x"⟩ * ⟨"out[1]"⟩;
      "x * out[1] - 1" ←ₐ ⟨"x * out[1]"⟩ - ⟨"1"⟩;
      ?₀ ⟨"x * out[1] - 1"⟩
    )
  (List.foldr And True) $ List.map (λ e ↦ e = 0) state'.constraints

theorem is0_original_nondet_iff_constraints
  {input output : List Felt}
  (h : input.length = 1 ∧ output.length = 2) :
  (is0_witness input = output ↔ is0_constraints input output) := by
  rcases h with ⟨hin, hout⟩
  have hin₁ := hin
  rcases input with _ | ⟨x, _ | _⟩ <;> simp at hin ; clear hin
  rcases output with _ | ⟨y₁, _ | ⟨y₂, ⟨_ | _⟩⟩⟩ <;> simp at hout ; clear hout
  unfold is0_witness
  by_cases hx : x = 0
  · rw [hx]
    rw [MLIR.run_Sequence_Assign_collapsible]
    simp only [Op.eval_getInput, List.getD_cons_zero, State.update_val]
    rw [MLIR.run_Sequence_Assign_collapsible]
    simp only [Op.eval_isz, Map.update_get, beq_iff_eq, ite_true, State.update_val]
    rw [MLIR.run_Sequence_Set_collapsible 1 (by simp only)] ; simp only
    rw [MLIR.run_Sequence_Assign_collapsible]
    simp only [Op.eval_inv, beq_iff_eq, State.update_val]
    sorry
  sorry

end Risc0
