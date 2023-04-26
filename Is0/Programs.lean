-- This file contains the MLIR program labeled `ORIGINAL` in the `nonzero-example` output.
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.FieldSimp

import Is0.Basic
import Is0.Ending
import Is0.Lemmas

namespace Risc0

open MLIRNotation

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
    output[0]   ←ᵢ ⟨"isZeroBit"⟩;
    "invVal"    ←ₐ Inv ⟨"x"⟩;
    output[1]   ←ᵢ ⟨"invVal"⟩
  state'.output

    -- %0 = cirgen.const 1
    -- %1 = cirgen.true
    -- %2 = cirgen.get %arg0[0] back 0 : <1, constant>
    -- %3 = cirgen.get %arg1[0] back 0 : <2, mutable>
    -- %4 = cirgen.and_eqz %1, %2 : <default>
    -- %5 = cirgen.and_cond %1, %3 : <default>, %4
    -- %6 = cirgen.sub %0 : <default>, %3 : <default>
    -- %7 = cirgen.get %arg1[1] back 0 : <2, mutable>
    -- %8 = cirgen.mul %2 : <default>, %7 : <default>
    -- %9 = cirgen.sub %8 : <default>, %0 : <default>
    -- %10 = cirgen.and_eqz %1, %9 : <default>
    -- %11 = cirgen.and_cond %5, %6 : <default>, %10

open MLIRNotation in
def is0_constraints (input : List Felt) (output : List Felt) : Prop :=
  let state' :=
    MLIR.run { felts := Map.empty
             , props := Map.empty
             , input := input
             , output := output
             , constraints := []
             } <|
    "1"         ←ₐ C 1;         -- %0 = cirgen.const 1
    "0"         ←ₐ C 0;
    "true"      ←ₐ ⊤;  -- %1 = cirgen.true
    "x"         ←ₐ input[0];  -- %2 = cirgen.get %arg0[0] back 0 : <1, constant>
    "out[0]"    ←ₐ output[0]; -- %3 = cirgen.get %arg1[0] back 0 : <2, mutable>
    "andEqz x"  ←ₐ ⟨"true"⟩ &₀ ⟨"x"⟩; -- %4 = cirgen.and_eqz %1, %2 : <default>
    "if out[0] then eqz x" ←ₐ guard ⟨"out[0]"⟩ & ⟨"true"⟩ with ⟨"andEqz x"⟩;  -- %5 = cirgen.and_cond %1, %3 : <default>, %4
    "1 - out[0]" ←ₐ ⟨"1"⟩ - ⟨"out[0]"⟩; -- %6 = cirgen.sub %0 : <default>, %3 : <default>
    "out[1]"         ←ₐ output[1]; -- %7 = cirgen.get %arg1[1] back 0 : <2, mutable>
    "x * out[1]"     ←ₐ ⟨"x"⟩ * ⟨"out[1]"⟩; -- %8 = cirgen.mul %2 : <default>, %7 : <default>
    "x * out[1] - 1" ←ₐ ⟨"x * out[1]"⟩ - ⟨"1"⟩; -- %9 = cirgen.sub %8 : <default>, %0 : <default>
    "other cond" ←ₐ ⟨"true"⟩ &₀ ⟨"x * out[1] - 1"⟩; -- %10 = cirgen.and_eqz %1, %9 : <default>
    "if other cond" ←ₐ guard ⟨"1 - out[0]"⟩ & ⟨"if out[0] then eqz x"⟩ with ⟨"other cond"⟩ -- %11 = cirgen.and_cond %5, %6 : <default>, %10
  -- (List.foldr And True) $ List.map (λ e ↦ e = 0) state'.constraints
  (state'.props "if other cond").getD True

open MLIR in
theorem is0_original_nondet_iff_constraints
  {input output : List Felt}
  (h : input.length = 1 ∧ output.length = 2) :
  (is0_witness input = output ↔ is0_constraints input output) := by
  unfold is0_constraints
  rcases h with ⟨hin, hout⟩
  rcases input with _ | ⟨x, _ | _⟩ <;> simp at hin ; clear hin
  rcases output with _ | ⟨y₁, _ | ⟨y₂, ⟨_ | _⟩⟩⟩ <;> simp at hout ; clear hout
  -- unfold is0_witness
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_getInput, List.getD_cons_zero, State.update_val]
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_const, State.update_val]
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_isz, Map.update_get, beq_iff_eq, ite_true, State.update_val]
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_getInput, List.getD_cons_zero, State.update_val]
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_getOutput, List.getD_cons_zero, State.update_val]
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp
  rw [Map.update_update_get (by decide)]
  simp only [Option.some.injEq, forall_apply_eq_imp_iff', Op.eval.match_2.eq_2]
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [
    Op.eval_andCond, Map.update_get, beq_iff_eq, Option.some.injEq, eq_iff_iff, true_iff,
    State.update_constraint]
  rw [Map.update_update_get (by decide)]
  simp only [true_and]
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_sub, Map.update_get, Option.some.injEq, forall_apply_eq_imp_iff', State.update_val]
  rw [Map.update_get' 1 (by simp) _]
  swap
  rw [Map.update_get' 1] <;> decide
  simp only
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_getOutput, List.getD_cons_succ, List.getD_cons_zero, State.update_val]
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_mul, Map.update_get, Option.some.injEq, forall_apply_eq_imp_iff', State.update_val]
  rw [Map.update_get' x] <;> try decide
  swap
  rw [Map.update_get' x] <;> try decide
  rw [Map.update_update_get (by decide)]
  simp only
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_sub, Map.update_get, Option.some.injEq, State.update_val]
  rw [Map.update_get' 1] <;> try decide
  swap
  rw [Map.update_get' 1] <;> try decide
  rw [Map.update_get' 1] <;> try decide
  rw [Map.update_get' 1] <;> try decide
  rw [Map.update_get' 1] <;> try decide
  simp
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_andEqz, Map.update_get, Option.some.injEq, forall_apply_eq_imp_iff',
  State.update_constraint]
  rw [Map.update_get' True] <;> try decide
  swap
  rw [Map.update_update_get (by decide)]
  simp only [true_and]
  rw [MLIR.run_assign]
  simp only [Op.eval_andCond, Map.update_get, beq_iff_eq, Option.some.injEq, eq_iff_iff,
  State.update_constraint, Option.getD_some]
  rw [Map.update_get' (Sub.sub 1 y₁)] <;> try decide
  swap
  rw [Map.update_get' (Sub.sub 1 y₁)] <;> try decide
  rw [Map.update_get' (Sub.sub 1 y₁)] <;> try decide
  simp
  rfl
  rw [Map.update_get' (if y₁ = 0 then True else x = 0)] <;> try decide
  swap
  simp
  simp
  generalize h :
    (if Sub.sub 1 y₁ = 0 then
      if y₁ = 0 then True else x = 0
        else (if y₁ = 0 then True else x = 0) ∧ HSub.hSub (HMul.hMul x y₂) 1 = 0) = finalCond
  unfold is0_witness
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_getInput, List.getD_cons_zero, State.update_val]
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_isz, Map.update_get, beq_iff_eq, State.update_val]
  rw [MLIR.run_Sequence_Set_collapsible (if x = 0 then 1 else 0)]
  swap
  simp
  simp only
  rw [MLIR.run_Sequence_Assign_collapsible]
  simp only [Op.eval_inv, beq_iff_eq, State.update_val]
  rw [Map.update_update_get (by decide)]
  simp only
  rw [MLIR.run_set]
  simp only [Map.update_get]
  apply Iff.intro
  · intros h₁
    subst h
    by_cases eq : x = 0 <;> simp [eq]
    · by_cases eq₁ : y₁ = 0 <;> simp [eq₁]
      subst eq₁
      subst eq
      simp at h₁
      simp [List.set] at h₁
      subst eq
      simp at h₁
      simp [List.set] at h₁
      rcases h₁ with ⟨h₁, h₂⟩
      subst h₁
      subst h₂
      simp
    · by_cases eq₁ : y₁ = 0 <;> simp [eq₁]
      · subst eq₁
        simp [List.set] at h₁
        rw [←h₁.2]
        simp [eq]
      · simp [eq, eq₁, List.set] at h₁
        tauto
  -- Other directioon
  have kekW : x ≠ 0 := sorry
  subst h
  intros h
  simp [kekW]
  by_cases eq : y₁ = 0 <;> simp [eq] at *
  · simp at h
    simp [List.set]
    field_simp [h]
    rw [←add_left_inj 1] at h
    simp at h
    rw [←h]
    ring
  · simp [List.set] at h
    field_simp [h]
    simp [List.set]
    by_cases eq₁ : y₁ = 0 <;> simp [*] at *
end Risc0
