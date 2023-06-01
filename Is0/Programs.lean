-- This file contains the MLIR program labeled `ORIGINAL` in the `nonzero-example` output.
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.FieldSimp

import Is0.Basic
import Is0.Lemmas

namespace Risc0

open MLIRNotation

def is0_witness (input : List Felt) : List Felt :=
  let state' :=
    MLIR.runProgram (st := 
      { felts := Map.empty
      , props := Map.empty
      , input := input
      , output := [42, 42]
      , constraints := []
      }) <|
    "1"         ←ₐ .Const 1;
    "x"         ←ₐ input[0];
    nondet (
      "isZeroBit" ←ₐ ??₀⟨"x"⟩;
      output[0]   ←ᵢ ⟨"isZeroBit"⟩;
      "invVal"    ←ₐ Inv ⟨"x"⟩;
      output[1]   ←ᵢ ⟨"invVal"⟩  
    );
    "arg1[0]"   ←ₐ output[0];
    guard ⟨"arg1[0]"⟩ then
      ?₀ ⟨"x"⟩;
    "1 - arg1[0]" ←ₐ .Sub ⟨"1"⟩ ⟨"arg1[0]"⟩;
    guard ⟨"1 - arg1[0]"⟩ then
      ("arg1[1]"        ←ₐ output[1];
      "x * arg1[1]"     ←ₐ .Mul ⟨"x"⟩ ⟨"arg1[1]"⟩;
      "x * arg1[1] - 1" ←ₐ .Sub ⟨"x * arg1[1]"⟩ ⟨"1"⟩;
      ?₀ ⟨"x * arg1[1] - 1"⟩)
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

def is0_constraints (input output : List Felt) : Prop :=
  let state' :=
    MLIR.runProgram (st :=
      { felts := Map.empty
      , props := Map.empty
      , input := input
      , output := output
      , constraints := []
      }) <|
    -- %0 = cirgen.const 1
    "1"         ←ₐ C 1; 
    "0"         ←ₐ C 0;
    -- %1 = cirgen.true
    "true"      ←ₐ ⊤;  
    -- %2 = cirgen.get %arg0[0] back 0 : <1, constant>
    "x"         ←ₐ input[0];
    -- %3 = cirgen.get %arg1[0] back 0 : <2, mutable>
    "out[0]"    ←ₐ output[0];
    -- %4 = cirgen.and_eqz %1, %2 : <default>
    "andEqz x"  ←ₐ ⟨"true"⟩ &₀ ⟨"x"⟩;
    -- %5 = cirgen.and_cond %1, %3 : <default>, %4
    "if out[0] then eqz x" ←ₐ guard ⟨"out[0]"⟩ & ⟨"true"⟩ with ⟨"andEqz x"⟩;  
    -- %6 = cirgen.sub %0 : <default>, %3 : <default>
    "1 - out[0]" ←ₐ Op.Sub ⟨"1"⟩ ⟨"out[0]"⟩;
    -- %7 = cirgen.get %arg1[1] back 0 : <2, mutable>
    "out[1]"         ←ₐ output[1];
    -- %8 = cirgen.mul %2 : <default>, %7 : <default>
    "x * out[1]"     ←ₐ Op.Mul ⟨"x"⟩ ⟨"out[1]"⟩; 
    -- %9 = cirgen.sub %8 : <default>, %0 : <default>
    "x * out[1] - 1" ←ₐ Op.Sub ⟨"x * out[1]"⟩ ⟨"1"⟩;
    -- %10 = cirgen.and_eqz %1, %9 : <default>
    "other cond" ←ₐ ⟨"true"⟩ &₀ ⟨"x * out[1] - 1"⟩; 
    -- %11 = cirgen.and_cond %5, %6 : <default>, %10
    "if other cond" ←ₐ guard ⟨"1 - out[0]"⟩ & ⟨"if out[0] then eqz x"⟩ with ⟨"other cond"⟩ 
  (state'.props "if other cond").getD True
      
section tactics

open Lean Elab Tactic

elab "MLIR" : tactic => do
  evalTactic <| ← `(
    tactic| repeat ( first |
      rw [MLIR.run_Sequence_Assign_collapsible] |
      rw [MLIR.run_Sequence_Set_collapsible] |
      rw [MLIR.run_Sequence_If_collapsible] |
      rw [MLIR.run_Sequence_nondet_collapsible] |
      rw [MLIR.run_If_collapsible] |
      rw [MLIR.run_Sequence_Eqz_collapsible] |
      rw [MLIR.run_Set_collapsible] |
      rw [MLIR.run_Eqz_collapsible]
      all_goals try rfl
      simp
    )
  )
  evalTactic <| ← `(tactic| try rw [MLIR.run_assign])
  evalTactic <| ← `(tactic| simp)

elab "MLIR_state" : tactic => do
  evalTactic <| ← `(tactic| repeat rw [Map.update_get'])
  evalTactic <| ← `(tactic| all_goals try decide)
  evalTactic <| ← `(tactic| all_goals try rfl)
  evalTactic <| ← `(tactic| all_goals simp only)
  evalTactic <| ← `(tactic| simp)

elab "MLIR_states" : tactic => do
  evalTactic <| ← `(tactic| repeat MLIR_state)

end tactics

set_option maxHeartbeats 1000000 in
lemma is0_constraints_closed_form {x y₁ y₂ : Felt} :
    is0_constraints [x] [y₁, y₂]
  ↔ (if 1 - y₁ = 0 then if y₁ = 0 then True else x = 0 else (if y₁ = 0 then True else x = 0) ∧ x * y₂ - 1 = 0) := by
  unfold is0_constraints MLIR.runProgram
  MLIR
  MLIR_states

lemma is0_constraints_simplified
  {input is_0 inv_of_input : Felt} :
  is0_constraints [input] [is_0, inv_of_input] ↔
    if is_0 = 1 then
      input = 0
    else if is_0 = 0 then
      ¬input = 0 ∧ input * inv_of_input = 1
    else
      True
  := by
  simp [is0_constraints_closed_form] -- get the full nested if form of is0_constraints
  repeat all_goals split
  all_goals simp [*] at *
  case inl.inr.inr one_sub_is_0_eq_0 _ is_0_neq_1 =>
    rewrite [sub_eq_iff_eq_add, zero_add] at one_sub_is_0_eq_0
    rewrite [one_sub_is_0_eq_0] at is_0_neq_1
    contradiction
  case inr.inl.inr is_0_eq_0 _ _ =>
    rewrite [sub_eq_iff_eq_add, zero_add]
    apply Iff.intro
    case mpr =>
      intro h
      exact And.right h
    case mp =>
      intro prod_inv_eq_one
      apply And.intro
      case left =>
        intro input_is_zero
        rewrite [input_is_zero] at prod_inv_eq_one
        aesop
      case right =>
        exact prod_inv_eq_one
  case inr.inr.inr =>
    sorry

lemma attempt2 {input is0 inv : Felt} :
  (if 1 - is0 = 0 then if is0 = 0 then True else input = 0 else (if is0 = 0 then True else input = 0) ∧ input * inv - 1 = 0)
   ↔
  ((input = 0 ∧ is0 = 1) ∨ (¬input = 0 ∧ input * inv = 1 ∧ is0 = 0)) := by
  by_cases input = 0
  . aesop
    rewrite [sub_eq_iff_eq_add, zero_add] at * --had to do this because it won't recognise h✝
    simp [*]
  . simp [*]
    by_cases is0 = 0
    . simp [h, sub_eq_iff_eq_add, zero_add]
    . simp [*]
#check if_pos
lemma attempt3
  {input is_0 inv_of_input : Felt} :
  (if 1 - is_0 = 0 then if is_0 = 0 then True else input = 0 else (if is_0 = 0 then True else input = 0) ∧ input * inv_of_inpu - 1 = 0) ↔
    if is_0 = 1 then
      input = 0
    else 
      input * inv_of_input = 1
  := by
  by_cases input = 0
  . have h₁: 1 - is_0 = 0 ↔ is_0 = 1 := by simp [sub_eq_iff_eq_add, zero_add];
    simp [*]
    simp only [sub_eq_iff_eq_add, zero_add]
    rfl
  -- repeat all_goals split
  -- all_goals simp [*] at *
  -- case inr.inl is0_eq_0 _ =>
  --   aesop
  --   rewrite [sub_eq_iff_eq_add, zero_add] at a
  --   exact a
  -- case inr.inr h₁ h₂ h₃ =>
  --   rewrite [sub_eq_iff_eq_add, zero_add] at h₁
  --   exact absurd h₁.symm h₃

  -- case inl.inr.inr one_sub_is_0_eq_0 _ is_0_neq_1 =>
  --   rewrite [sub_eq_iff_eq_add, zero_add] at one_sub_is_0_eq_0
  --   rewrite [one_sub_is_0_eq_0] at is_0_neq_1
  --   contradiction
  -- case inr.inl.inr is_0_eq_0 _ _ =>
  --   rewrite [sub_eq_iff_eq_add, zero_add]
  --   apply Iff.intro
  --   case mpr =>
  --     intro h
  --     exact And.right h
  --   case mp =>
  --     intro prod_inv_eq_one
  --     apply And.intro
  --     case left =>
  --       intro input_is_zero
  --       rewrite [input_is_zero] at prod_inv_eq_one
  --       aesop
  --     case right =>
  --       exact prod_inv_eq_one
  -- case inr.inr.inr =>
  --   sorry

  -- case inl.inl.inl _ is_0_eq_0 is_0_eq_1 =>
  --   rw [is_0_eq_0] at is_0_eq_1
  --   contradiction
  -- case inl.inl.inr one_sub_is_0_eq_0 is_0_eq_0 _ =>
  --   rw [is_0_eq_0] at one_sub_is_0_eq_0
  --   contradiction
  -- case inl.inr one_sub_is_0_eq_0 is_0_neq_0 =>
  --   rw [sub_eq_iff_eq_add, zero_add] at one_sub_is_0_eq_0
  --   rw [one_sub_is_0_eq_0]
  --   simp
  -- case inr is_0_neq_1 =>
  --   rw [sub_eq_iff_eq_add, zero_add] at is_0_neq_1
  --   rw [sub_eq_iff_eq_add, zero_add]
  --   repeat split



  -- repeat split
  -- all_goals simp [*] at *
  -- repeat split
  -- all_goals simp [*] at *
  -- split



set_option maxHeartbeats 400000 in
lemma is0_witness_closed_form {x y₁ y₂ : Felt} :
  is0_witness [x] = [y₁, y₂] ↔ (if x = 0 then 1 else 0) = y₁ ∧ (if x = 0 then 0 else x⁻¹) = y₂ := by
  unfold is0_witness MLIR.runProgram
  MLIR
  MLIR_states
  simp [List.set]

end Risc0


