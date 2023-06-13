-- This file contains the MLIR program labeled `ORIGINAL` in the `nonzero-example` output.
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp

import Risc0.Basic
import Risc0.Lemmas
import Risc0.Wheels
import Risc0.MlirTactics

namespace Risc0

open MLIRNotation

def is0_initial_state (input : Felt) (output : BufferAtTime) : State :=
  { buffers := Map.fromList [(⟨"input"⟩, [[.some input]]), (⟨"output"⟩, [output])]
  , bufferWidths := Map.fromList [(⟨"input"⟩, 1), (⟨"output"⟩, 2)]
  , constraints := []
  , cycle := 0
  , felts := Map.empty
  , props := Map.empty
  , vars := [⟨"input"⟩, ⟨"output"⟩]
  , isFailed := false
  }

def is0_initial_state' (input output : List (Option Felt))
                       (hIn : input.length = 1)
                       (hOut : output.length = 2) :=
  State.init 1 2 input output hIn hOut

theorem justToShowInitialEquiv {input : Felt} {output : BufferAtTime} (hOut : output.length = 2) :
        is0_initial_state input output = is0_initial_state' [Option.some input] output rfl hOut := rfl

def is0_witness_initial_state (input : Felt) : State := is0_initial_state input ([.none, .none])

theorem is0_initial_state_wf {input : Felt} {output : BufferAtTime} {hLen : output.length = 2} :
  is0_initial_state input output |>.WellFormed := by
    rw [justToShowInitialEquiv hLen]
    exact State.valid_init'
    
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


def is0_witness (input : Felt) : BufferAtTime :=
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
  
set_option maxHeartbeats 2000000 in
lemma is0_constraints_closed_form {x y₁ y₂ : Felt} :
    (is0_constraints x ([y₁, y₂]))
  ↔ (if 1 - y₁ = 0 then if y₁ = 0 then True else x = 0 else (if y₁ = 0 then True else x = 0) ∧ x * y₂ - 1 = 0) := by
  sorry
  -- unfold is0_constraints MLIR.runProgram
  -- unfold is0_initial_state
  -- simp [MLIR.run_seq_def]
  -- simp [MLIR.run_ass_def]
  -- MLIR_states

  -- simp [MLIR.run_seq_def]
  -- unfold is0_initial_state
  -- simp
  -- simp [MLIR.run_ass_def]

  -- save
  
  
  
  -- MLIR_states
  -- aesop

set_option maxHeartbeats 2000000 in
lemma is0_witness_closed_form {x y₁ y₂ : Felt} :
  is0_witness x = [y₁, y₂] ↔ (if x = 0 then 1 else 0) = y₁ ∧ (if x = 0 then 0 else x⁻¹) = y₂ := by
  sorry

  -- Just playing around to see what's slow.
  -- unfold is0_witness MLIR.runProgram
  -- simp [is0_witness_initial_state, is0_initial_state]
  -- rw [MLIR.run_seq_def]
  -- rw [MLIR.run_ass_def]
  -- rw [MLIR.run_seq_def]
  -- rw [MLIR.run_ass_def]
  -- rw [MLIR.run_seq_def]
  -- simp_op
  -- MLIR_states
  -- rw [MLIR.run_nondet]
  -- rw [MLIR.run_seq_def]
  -- rw [MLIR.run_ass_def]
  -- simp_op
  -- -- MLIR_states
  -- -- save
  -- rw [MLIR.run_seq_def]
  -- rw [MLIR.run_if] <;> all_goals try rfl
  -- rw [MLIR.run_seq_def]
  -- rw [MLIR.run_ass_def]
  -- simp_op
  -- rw [MLIR.run_seq_def]
  -- rw [MLIR.run_if] <;> all_goals try rfl
  -- rw [MLIR.run_seq_def]
  -- rw [MLIR.run_ass_def]
  

  -- rw [MLIR.run_seq_def]
  -- rw [MLIR.run_if]
  -- rw [MLIR.run_seq_def]
  -- rw [MLIR.run_ass_def]
  -- simp_op
  -- MLIR_states
  -- save
  -- rw [MLIR.run_seq_def]
  -- rw [MLIR.run_ass_def]
  -- rw [MLIR.run_seq_def]
  -- rw [MLIR.run_ass_def]
  -- rw [MLIR.run_seq_def]
  -- rw [MLIR.run_ass_def]
  -- save
  -- rw [MLIR.run_seq_def]
  -- rw [MLIR.run_ass_def]




  -- simp
  -- rw [MLIR.run_set_output]
  -- rw [MLIR.run_if]
  -- rw [MLIR.run_nondet]
  -- rw [MLIR.run_eqz]
  -- MLIR
  -- MLIR_states

end Risc0
