-- This file contains the MLIR program labeled `ORIGINAL` in the `nonzero-example` output.
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Is0.Basic
import Is0.Ending
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
  rcases input with _ | ⟨x, _ | _⟩ <;> simp at hin ; clear hin
  rcases output with _ | ⟨y₁, _ | ⟨y₂, ⟨_ | _⟩⟩⟩ <;> simp at hout ; clear hout
  unfold is0_witness
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_getInput, List.getD_cons_zero, State.update_val]
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_isz, Map.update_get, beq_iff_eq, ite_true, State.update_val]
  rw [MLIR.run_Sequence_Set_collapsible (if x = 0 then 1 else 0) (by simp only [Map.update_get])] ; simp only
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_inv, beq_iff_eq, State.update_val]
  rw [Map.update_update_get (by decide)]
  simp only [inv_zero, ite_self]
  rw [@run_setOutput_of_some _ 1 (if x = 0 then 0 else x⁻¹) _ (by simp only [Map.update_get])] ; simp only
  unfold List.set List.set ; simp only [List.cons.injEq, and_true]
  unfold is0_constraints
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_const_one, State.update_val]
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_getInput, List.getD_cons_zero, State.update_val]
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_getOutput, List.getD_cons_zero, State.update_val]
  rw [MLIR.run_Sequence_If_collapsible y₁ (by simp only [Map.update_get])]
  simp only [beq_iff_eq]
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_sub, Map.update_get, Option.some.injEq, forall_apply_eq_imp_iff', State.update_val]
  rw [@Map.update_get' _ _ _ _ "1" "out[0]" 1 _ (by simp) _]
  swap
  rw [Map.update_update_get (by simp)]
  simp only
  rw [MLIR.run_If_collapsible (1 - y₁) (by simp)]
  simp only [beq_iff_eq]
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_getOutput, List.getD_cons_succ, List.getD_cons_zero, State.update_val]
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_mul, Map.update_get, Option.some.injEq, forall_apply_eq_imp_iff', State.update_val]
  rw [@Map.update_get' _ _ _ _ "x" "out[1]" x _ (by simp) _] ; simp only
  swap
  rw [@Map.update_get' _ _ _ _ "x" "1 - out[0]" x _ (by simp) _] ; simp only
  rw [@Map.update_get' _ _ _ _ "x" "out[0]" x _ (by simp) _] ; simp only
  simp only [Map.update_get]
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_sub, Map.update_get, Option.some.injEq, State.update_val]
  rw [@Map.update_get' _ _ _ _ "1" "x * out[1]" 1 _ (by simp) _] ; simp only
  swap
  rw [@Map.update_get' _ _ _ _ "1" "out[1]" 1 _ (by simp) _] ; simp only
  rw [@Map.update_get' _ _ _ _ "1" "1 - out[0]" 1 _ (by simp) _] ; simp only
  rw [@Map.update_get' _ _ _ _ "1" "out[0]" 1 _ (by simp) _] ; simp only
  rw [@Map.update_get' _ _ _ _ "1" "x" 1 _ (by simp) _] ; simp only
  rw [@run_Eqz_of_some _ (x * y₂ - 1) _ (by simp)] ; simp only
  rw [MLIR.run_Sequence_Eqz_collapsible x]
  swap
  simp only
  rw [Map.update_update_get (by simp)]
  simp only
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_sub, Map.update_get, Option.some.injEq, forall_apply_eq_imp_iff', State.update_val]
  rw [@Map.update_get' _ _ _ _ "1" "out[0]" 1 _ (by simp) (by rw [Map.update_update_get (by simp)])] ; simp only
  rw [MLIR.run_If_collapsible (1 - y₁) (by simp)]
  simp only [beq_iff_eq]
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_getOutput, List.getD_cons_succ, List.getD_cons_zero, State.update_val]
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_mul, Map.update_get, Option.some.injEq, forall_apply_eq_imp_iff', State.update_val]
  rw [@Map.update_get' _ _ _ _ "x" _ x _ (by simp) _] ; simp only
  swap
  rw [@Map.update_get' _ _ _ _ "x" _ x _ (by simp) _] ; simp only
  rw [@Map.update_get' _ _ _ _ "x" _ x _ (by simp) _] ; simp only
  simp only [Map.update_get]
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_sub, Map.update_get, Option.some.injEq, State.update_val]
  rw [@Map.update_get' _ _ _ _ "1" _ 1 _ (by simp) _] ; simp only
  swap
  rw [@Map.update_get' _ _ _ _ "1" _ 1 _ (by simp) _] ; simp only
  rw [@Map.update_get' _ _ _ _ "1" _ 1 _ (by simp) _] ; simp only
  rw [@Map.update_get' _ _ _ _ "1" _ 1 _ (by simp) _] ; simp only
  rw [@Map.update_get' _ _ _ _ "1" _ 1 _ (by simp) _] ; simp only
  rw [@run_Eqz_of_some _ (x * y₂ - 1) _ (by simp)] ; simp only
  rw [State.if_constraints]
  simp only [State.if_constraints]
  apply ending

end Risc0
