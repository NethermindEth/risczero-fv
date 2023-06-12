-- This file contains the MLIR program labeled `ORIGINAL` in the `nonzero-example` output.
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp

import Risc0.Basic
import Risc0.Lemmas
import Risc0.Wheels

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

def is0_witness_prog : MLIRProgram :=
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

def is0_witness (input : Felt) : BufferAtTime :=
    let st' := MLIR.runProgram (st := is0_witness_initial_state input) <| is0_witness_prog
  (st'.buffers ⟨"output"⟩ |>.get!.getLast!)

def is0_witness₀ : MLIRProgram := "1" ←ₐ .Const 1;
                                  "x" ←ₐ Op.Get ⟨"input"⟩ 0 0
def is0_witness₁ : MLIRProgram := nondet (
    "isZeroBit" ←ₐ ??₀⟨"x"⟩;
    ⟨"output"⟩[0]   ←ᵢ ⟨"isZeroBit"⟩;
    "invVal"    ←ₐ Inv ⟨"x"⟩;
    ⟨"output"⟩[1]   ←ᵢ ⟨"invVal"⟩  
  )
def is0_witness₂ : MLIRProgram := "arg1[0]" ←ₐ .Get ⟨"output"⟩ 0 0
def is0_witness₃ : MLIRProgram := guard ⟨"arg1[0]"⟩ then ?₀ ⟨"x"⟩
def is0_witness₄ : MLIRProgram := "1 - arg1[0]" ←ₐ .Sub ⟨"1"⟩ ⟨"arg1[0]"⟩
def is0_witness₅ : MLIRProgram :=
  guard ⟨"1 - arg1[0]"⟩ then
    "arg1[1]"        ←ₐ .Get ⟨"output"⟩ 0 1;
    "x * arg1[1]"     ←ₐ .Mul ⟨"x"⟩ ⟨"arg1[1]"⟩;
    "x * arg1[1] - 1" ←ₐ .Sub ⟨"x * arg1[1]"⟩ ⟨"1"⟩;
    ?₀ ⟨"x * arg1[1] - 1"⟩

lemma is0_witness_per_partes {input} :
  Γ (is0_witness_initial_state input) ⟦is0_witness_prog⟧ =
  Γ (is0_witness_initial_state input)
    ⟦is0_witness₀; is0_witness₁; is0_witness₂; is0_witness₃; is0_witness₄; is0_witness₅⟧ := by 
  unfold is0_witness_prog
  unfold is0_witness₀
  unfold is0_witness₁
  unfold is0_witness₂ 
  unfold is0_witness₃
  unfold is0_witness₄
  unfold is0_witness₅
  rw [←MLIR.seq_assoc]

def is0_constraints (input : Felt) (output : List (Option Felt)) : Prop :=
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

open Op in
elab "simp_op" : tactic => do
  evalTactic <| ← `( tactic|
    simp only [
      eval_const, eval_true, eval_getBuffer, eval_sub,
      eval_mul, eval_isz, eval_inv, eval_andEqz, eval_andCond
    ]
  )

elab "MLIR" : tactic => do
  evalTactic <| ← `(
    tactic| repeat ( first |
      rw [MLIR.run_ass_def] | rw [MLIR.run_set_output] | rw [MLIR.run_if] |
      rw [MLIR.run_nondet] | rw [MLIR.run_eqz] |
      rw [MLIR.run_seq_def] 
      all_goals try rfl
      simp_op
    )
  )
  evalTactic <| ← `(tactic| try rw [MLIR.run_ass_def])
  evalTactic <| ← `(tactic| simp)

elab "MLIR_state" : tactic => do
  evalTactic <| ← `(tactic| repeat rw [Map.update_get_skip])
  evalTactic <| ← `(tactic| all_goals try decide)
  evalTactic <| ← `(tactic| all_goals try rfl)
  evalTactic <| ← `(tactic| all_goals simp only)
  -- evalTactic <| ← `(tactic| simp)

elab "MLIR_states" : tactic => do
  evalTactic <| ← `(tactic| repeat MLIR_state)

elab "MLIR_statement" : tactic => do
  evalTactic <| ← `(
    tactic| (
      rewrite [MLIR.run_seq_def]
      repeat (
        first
        | rewrite [MLIR.run_ass_def]
        | rewrite [MLIR.run_set_output]
        | rewrite [MLIR.run_if]
        | rewrite [MLIR.run_nondet]
        | rewrite [MLIR.run_eqz]
      )
      simp_op
    )
  )

end tactics

lemma run_preserves_width {st : State} : (st.bufferWidths bufferVar) = (MLIR.run program st).bufferWidths bufferVar := by
  sorry
  -- induction program with
  --   | Assign name op => {
  --     unfold MLIR.run State.update Op.eval
  --     aesop
  --   }
  --   | Eqz x => {
  --     unfold MLIR.run
  --     aesop
  --   }
  --   | If cond branch h_branch => {
  --     cases st.felts cond with
  --       | some x => {
  --         unfold MLIR.run
  --         aesop
  --       }
  --       | none => {
  --         unfold MLIR.run
  --         aesop
  --       }
  --   }
  --   | Nondet block h_block => {
  --     unfold MLIR.run
  --     aesop
  --   }
  --   | Sequence a b h₁ h₂ => {
  --     unfold MLIR.run
  --     rewrite [h₂]
  --   }
  --   | Fail         => {

  --   }
  --   | Set buf offset val => {

  --   }
  --   | SetGlobal buf offset val => {

  --   }

-- set_option maxHeartbeats 2000000 in
-- lemma is0_constraints_closed_form {x: Felt} {y₁ y₂ : Option Felt} :
--     (is0_constraints x ([y₁, y₂]))
--   ↔ (if 1 - y₁.get! = 0 then if y₁.get! = 0 then True else x = 0 else (if y₁.get! = 0 then True else x = 0) ∧ x * y₂.get! - 1 = 0) := by
--   unfold is0_constraints MLIR.runProgram
--   let s₁ : State := is0_initial_state x ([y₁, y₂])
--   have hs₁ : is0_initial_state x ([y₁, y₂]) = s₁ := by rfl
--   MLIR_statement
--   MLIR_statement
--   MLIR_statement
--   MLIR_statement
--   rewrite [hs₁]
--   let s₂ : State := s₁["1"] := some (Lit.Val 1)
--   have hs₂ : s₁.update "1" (some (Lit.Val 1)) = s₂ := by rfl
--   rewrite [hs₂]
--   let s₃ : State := s₂["0"] := some (Lit.Val 0)
--   have hs₃ : s₂.update "0" (some (Lit.Val 0)) = s₃ := by rfl
--   rewrite [hs₃]
--   let s₄ : State := s₃["true"] := some (Lit.Constraint True)
--   have hs₄ : s₃.update "true" (some (Lit.Constraint True)) = s₄ := by rfl
--   rewrite [hs₄]
--   have h₁ : 0 ≤ s₄.cycle := by simp
--   have h_input₄ : ⟨"input"⟩  ∈ s₄.vars := by {
--     simp
--     unfold is0_initial_state
--     simp
--   }
--   have h_input_width₄ : 0 < s₄.bufferWidths.get! ⟨"input"⟩ := by {
--     unfold Map.get!
--     simp [run_preserves_width]
--     unfold is0_initial_state
--     simp
--   }
--   -- infoview stops working here
--   have h_input_valid : (s₄.buffers.get! ⟨"input"⟩).get! (s₄.cycle - Back.toNat 0, 0) = some x := by {
    
--   }
--   -- simp [MLIR.run_ass_def]
--   -- MLIR_states

--   -- simp [MLIR.run_seq_def]
--   -- unfold is0_initial_state
--   -- simp
--   -- simp [MLIR.run_ass_def]

--   -- save
  
  
  
--   -- MLIR_states
--   -- aesop

-- lemma is0_witness₀_state {x y₁ y₂ : Felt} :  
--   ∀ st', MLIR.runProgram is0_witness₀ 


-- lemma is0_witness₀_closed_form {x : Felt} :
--   MLIR.runProgram is0_witness₀ (is0_witness_initial_state x) = 

def is0_witness₀_final_state (x : Felt) : State := (((is0_witness_initial_state x)["1"] := some (Lit.Val 1))["x"] :=
                if
                    0 ≤ ((is0_witness_initial_state x)["1"] := some (Lit.Val 1)).cycle ∧
                      { name := "input" } ∈ ((is0_witness_initial_state x)["1"] := some (Lit.Val 1)).vars ∧
                        0 <
                            Map.get! ((is0_witness_initial_state x)["1"] := some (Lit.Val 1)).bufferWidths
                              { name := "input" } ∧
                          Option.isSome
                              (Buffer.get!
                                (Map.get! ((is0_witness_initial_state x)["1"] := some (Lit.Val 1)).buffers
                                  { name := "input" })
                                (((is0_witness_initial_state x)["1"] := some (Lit.Val 1)).cycle - Back.toNat 0, 0)) =
                            true then
                  some
                    (Lit.Val
                      (Option.get!
                        (Buffer.get!
                          (Map.get! ((is0_witness_initial_state x)["1"] := some (Lit.Val 1)).buffers { name := "input" })
                          (((is0_witness_initial_state x)["1"] := some (Lit.Val 1)).cycle - Back.toNat 0, 0)))) else none)

lemma is0_witness₀_closed_form {x y₁ y₂ : Felt} :
  MLIR.runProgram is0_witness₀ (is0_witness_initial_state x) = is0_witness₀_final_state x := by
  unfold is0_witness₀ MLIR.runProgram is0_witness₀_final_state; simp only
  MLIR
  MLIR_states

lemma x_simp {x : Felt} :
  State.felts (is0_witness₀_final_state x) { name := "x" } = some x := by
  unfold is0_witness₀_final_state
  simp only [State.update_val, zero_le, List.find?, ge_iff_le, true_and]
  simp only [List.find?, ge_iff_le]
  unfold is0_witness_initial_state
  simp only [List.find?, ge_iff_le]
  unfold is0_initial_state
  simp only [Map.fromList_cons, Map.fromList_nil, List.find?, List.mem_cons, ge_iff_le, tsub_eq_zero_of_le,
  true_and]
  rfl


lemma is0_witness_closed_form {x y₁ y₂ : Felt} {h: x = 0} :
  ((MLIR.runProgram is0_witness₁ (is0_witness₀_final_state x)).buffers ⟨"output"⟩ |>.get!.getLast!) = [y₁, y₂] ↔ _ := by
  unfold is0_witness₁ MLIR.runProgram; simp only
  rewrite [MLIR.run_nondet]
  MLIR_statement
  rewrite [x_simp]
  simp only [Option.get!_of_some]
  subst h
  simp only [ite_true]
  MLIR_statement
  rewrite [MLIR.run_set_def]
  simp only [State.update_val]
  by_cases eq: ((is0_witness₀_final_state 0).felts[{ name := "isZeroBit" }] := 1) ({ name := "isZeroBit" } : FeltVar) = some 1
  rw [eq]
  simp
  MLIR_statement
  simp only [State.update_val]
  simp only [State.felts]
  simp only [Map.update_get] at eq
  have hh : ((is0_witness₀_final_state 0).felts[{ name := "isZeroBit" }] := 1) { name := "isZeroBit" } := some (Lit.Val 1))  = some 1 := by {

  }
  rewrite [Map.update_get]
  MLIR_statement
  rewrite [MLIR.run_set_def]
  rewrite [MLIR.run_set_def]
  simp only [State.update_val]
  
  simp only [Option.get!_of_some]
  subst h
  simp [ite_true]
  rewrite [Map.update_get]
  simp_op
  rfl

#print is0_witness_closed_form

/-
⊢ ∀ {x y₁ y₂ : Felt},
  is0_witness x = Lean.Internal.coeM [y₁, y₂] ↔
    List.getLast!
        (Option.get!
          (State.buffers
            (Γ
              ((is0_witness_initial_state x["1"] := some (Lit.Val 1))["x"] :=
                if
                    0 ≤ (is0_witness_initial_state x["1"] := some (Lit.Val 1)).cycle ∧
                      { name := "input" } ∈ (is0_witness_initial_state x["1"] := some (Lit.Val 1)).vars ∧
                        0 < Map.get! { name := "input" } ∧
                          Option.isSome
                              (Buffer.get! (Map.get! { name := "input" })
                                ((is0_witness_initial_state x["1"] := some (Lit.Val 1)).cycle - Back.toNat 0, 0)) =
                            true then
                  some
                    (Lit.Val
                      (Option.get!
                        (Buffer.get! (Map.get! { name := "input" })
                          ((is0_witness_initial_state x["1"] := some (Lit.Val 1)).cycle - Back.toNat 0, 0))))
                else none) ⟦is0_witness₁; is0_witness₂; is0_witness₃; is0_witness₄; is0_witness₅⟧)
            { name := "output" })) =
      Lean.Internal.coeM [y₁, y₂]
-/
#print is0_witness_closed_form

set_option maxHeartbeats 2000000 in
lemma is0_witness_closed_form {x y₁ y₂ : Felt} :
  is0_witness x = [y₁, y₂] ↔ (if x = 0 then 1 else 0) = y₁ ∧ (if x = 0 then 0 else x⁻¹) = y₂ := by
  unfold is0_witness MLIR.runProgram; simp only
  rw [is0_witness_per_partes]
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
