-- This file contains the MLIR program labeled `ORIGINAL` in the `nonzero-example` output.
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp

import Is0.Basic
import Is0.Lemmas
import Is0.Wheels

namespace Risc0

open MLIRNotation

def is0_initial_state (input : Felt) (output : List Felt) : State :=
  { buffers := Map.fromList [(⟨"input"⟩, [[input]]), (⟨"output"⟩, [output])]
  , bufferWidths := Map.fromList [(⟨"input"⟩, 1), (⟨"output"⟩, 2)]
  , constraints := []
  , cycle := 0
  , felts := Map.empty
  , props := Map.empty
  , isFailed := False
  , vars := [⟨"input"⟩, ⟨"output"⟩]
  }

def is0_witness_initial_state (input : Felt) : State := is0_initial_state input ([42, 42])

def is0_initial_state_valid {input : Felt} {output : List Felt} {hLen : output.length = 2} : is0_initial_state input output |>.valid := by
  unfold is0_initial_state
  exact { distinct := by simp
          , hVars := by 
              intros var
              rw [Map.mem_eq]
              simp
              apply Iff.intro
              · intros h
                rcases h with h | h 
                simp
                subst h
                simp
                subst h
                simp only [Map.update_update_get]
                rfl
              · by_cases eq : var = ⟨"input"⟩ 
                subst eq
                tauto
                by_cases eq₁ : var = ⟨"output"⟩
                subst eq₁
                tauto
                rw [Map.update_get_not_equal]
                rw [Map.update_get_not_equal]
                simp only [Map.empty]
                tauto
                exact eq₁
                exact eq  
          , hCycle := by
              simp only [Map.fromList_cons, Map.fromList_nil, decide_False]
              intros var h
              simp at h
              by_cases eq : var = ⟨"input"⟩ 
              subst eq
              rw [getElem_eq]
              simp only [Map.update_get, Option.get_some, List.length_singleton, zero_add]
              by_cases eq₁ : var = ⟨"output"⟩ 
              subst eq₁
              rw [getElem_eq]    
              simp only [zero_add, Map.empty, Map.update, ite_true, ite_false, Option.get_some, List.length_singleton]
              simp
              rw [Map.mem_eq] at h
              rw [Map.update_get_not_equal eq] at h
              rw [Map.update_get_not_equal eq₁] at h
              simp only [Map.empty] at h 
          , hCols := by
              intros var
              apply Iff.intro
              · intros h
                simp at h
                rcases h with h | h
                · subst h
                  rw [Map.mem_eq]
                  simp only
                · subst h
                  rw [Map.mem_eq]
                  simp only
              · intros h
                simp at h
                by_cases eq : var = ⟨"input"⟩ 
                subst eq
                simp
                by_cases eq₁ : var = ⟨"output"⟩ 
                subst eq₁
                simp only
                rw [Map.mem_eq] at h
                rw [Map.update_get_not_equal] at h
                rw [Map.update_get_not_equal] at h
                simp only [Map.empty] at h
                exact eq₁
                exact eq 
          , hColsLen := by
              simp only [Map.fromList_cons, Map.fromList_nil, decide_False]
              unfold bufferLensConsistent
              simp only [List.getElem_eq_get]
              intros var h row x h₁
              simp at h
              have var_input_or_output : var ∈ [⟨"input"⟩,⟨"output"⟩] := by
                simp [Map.mem_fromList]
                sorry
                -- rewrite [Map.mem_unroll_assignment] at h
              sorry

              -- unfold cycleIsRows at row
              -- simp only [zero_add] at row
              -- by_cases eq : var = ⟨"input"⟩ 
              -- subst eq
              -- rw [Map.update_get]
              -- simp only [Option.some.injEq]
              -- simp
              -- sorry
              -- sorry 
    }


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


def is0_witness (input : Felt) : List Felt :=
    let st' := MLIR.runProgram (st := is0_witness_initial_state input) <|
    "1"         ←ₐ .Const 1;
    "x"         ←ₐ Op.Get ⟨"input"⟩ 0 0;
    nondet (
      "isZeroBit" ←ₐ ??₀⟨"x"⟩;
      ⟨"output"⟩[0]   ←ᵢ ⟨"isZeroBit"⟩;
      "invVal"    ←ₐ Inv ⟨"x"⟩;
      ⟨"output"⟩[1]   ←ᵢ ⟨"invVal"⟩  
    );
    "arg1[0]"   ←ₐ .Get ⟨"output"⟩ 0 0;
    guard ⟨"arg1[0]"⟩ then
      ?₀ ⟨"x"⟩;
    "1 - arg1[0]" ←ₐ .Sub ⟨"1"⟩ ⟨"arg1[0]"⟩;
    guard ⟨"1 - arg1[0]"⟩ then
      "arg1[1]"        ←ₐ .Get ⟨"output"⟩ 0 1;
      "x * arg1[1]"     ←ₐ .Mul ⟨"x"⟩ ⟨"arg1[1]"⟩;
      "x * arg1[1] - 1" ←ₐ .Sub ⟨"x * arg1[1]"⟩ ⟨"1"⟩;
      ?₀ ⟨"x * arg1[1] - 1"⟩
  (st'.buffers ⟨"output"⟩ |>.get!.getLast!)

def is0_constraints (input : Felt) (output : List Felt) : Prop :=
  let state' :=
    MLIR.runProgram (st := is0_initial_state input output) <|
    -- %0 = cirgen.const 1
    "1"         ←ₐ C 1; 
    "0"         ←ₐ C 0;
    -- %1 = cirgen.true
    "true"      ←ₐ ⊤;  
    -- %2 = cirgen.get %arg0[0] back 0 : <1, constant>
    "x"         ←ₐ .Get ⟨"input"⟩ 0 0;
    -- %3 = cirgen.get %arg1[0] back 0 : <2, mutable>
    "out[0]"    ←ₐ .Get ⟨"output"⟩ 0 0;
    -- %4 = cirgen.and_eqz %1, %2 : <default>
    "andEqz x"  ←ₐ ⟨"true"⟩ &₀ ⟨"x"⟩;
    -- %5 = cirgen.and_cond %1, %3 : <default>, %4
    "if out[0] then eqz x" ←ₐ guard ⟨"out[0]"⟩ & ⟨"true"⟩ with ⟨"andEqz x"⟩;  
    -- %6 = cirgen.sub %0 : <default>, %3 : <default>
    "1 - out[0]" ←ₐ Op.Sub ⟨"1"⟩ ⟨"out[0]"⟩;
    -- %7 = cirgen.get %arg1[1] back 0 : <2, mutable>
    "out[1]"         ←ₐ .Get ⟨"output"⟩ 0 1;
    -- %8 = cirgen.mul %2 : <default>, %7 : <default>
    "x * out[1]"     ←ₐ Op.Mul ⟨"x"⟩ ⟨"out[1]"⟩; 
    -- %9 = cirgen.sub %8 : <default>, %0 : <default>
    "x * out[1] - 1" ←ₐ Op.Sub ⟨"x * out[1]"⟩ ⟨"1"⟩;
    -- %10 = cirgen.and_eqz %1, %9 : <default>
    "other cond" ←ₐ ⟨"true"⟩ &₀ ⟨"x * out[1] - 1"⟩; 
    -- %11 = cirgen.and_cond %5, %6 : <default>, %10
    "if other cond" ←ₐ guard ⟨"1 - out[0]"⟩ & ⟨"if out[0] then eqz x"⟩ with ⟨"other cond"⟩ 
  (state'.props ⟨"if other cond"⟩).getD True
      
section tactics

open Lean Elab Tactic

elab "MLIR" : tactic => do
  evalTactic <| ← `(
    tactic| repeat ( first |
      rw [MLIR.run_seq_def] | rw [MLIR.run_ass_def] | rw [MLIR.run_set_output] | rw [MLIR.run_if] |
      rw [MLIR.run_nondet] |
      rw [MLIR.run_eqz]
      all_goals try rfl
      simp
    )
  )
  evalTactic <| ← `(tactic| try rw [MLIR.run_ass_def])
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
  
set_option maxHeartbeats 2000000 in
lemma is0_constraints_closed_form {x y₁ y₂ : Felt} :
    (is0_constraints x ([y₁, y₂]))
  ↔ (if 1 - y₁ = 0 then if y₁ = 0 then True else x = 0 else (if y₁ = 0 then True else x = 0) ∧ x * y₂ - 1 = 0) := by
  unfold is0_constraints MLIR.runProgram
  MLIR
  MLIR_states
  aesop
  
set_option maxHeartbeats 2000000 in
lemma is0_witness_closed_form {x y₁ y₂ : Felt} :
  is0_witness x = [y₁, y₂] ↔ (if x = 0 then 1 else 0) = y₁ ∧ (if x = 0 then 0 else x⁻¹) = y₂ := by
  unfold is0_witness MLIR.runProgram
  MLIR
  MLIR_states

end Risc0
