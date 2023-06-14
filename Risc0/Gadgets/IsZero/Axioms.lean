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

def is0_witness (st : State) : BufferAtTime :=
  is0_witness_prog.runProgram st |>.lastOutput

def is0_witness_initial (input : Felt) : BufferAtTime :=
  is0_witness_prog.runProgram (is0_witness_initial_state input) |>.lastOutput

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

abbrev is0_witness_program_full : MLIRProgram :=
  is0_witness₀; is0_witness₁; is0_witness₂; is0_witness₃; is0_witness₄; is0_witness₅

lemma is0_witness_per_partes {st : State} :
  Γ st ⟦is0_witness_prog⟧ =
  Γ st ⟦is0_witness_program_full⟧ := by 
  unfold is0_witness_program_full
         is0_witness_prog
         is0_witness₀ is0_witness₁ is0_witness₂ is0_witness₃ is0_witness₄ is0_witness₅
  rw [←MLIR.seq_assoc]

lemma is0_witness_per_partes_initial {input} :
  Γ (is0_witness_initial_state input) ⟦is0_witness_prog⟧ =
  Γ (is0_witness_initial_state input)
    ⟦is0_witness₀; is0_witness₁; is0_witness₂; is0_witness₃; is0_witness₄; is0_witness₅⟧ :=
  is0_witness_per_partes

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

-- elab "MLIR" : tactic => do
--   evalTactic <| ← `(
--     tactic| repeat ( first |
--       rw [MLIR.run_ass_def] | rw [MLIR.run_set_output] | rw [MLIR.run_if] |
--       rw [MLIR.run_nondet] | rw [MLIR.run_eqz] |
--       rw [MLIR.run_seq_def] 
--       all_goals try rfl
--       simp_op
--     )
--   )
--   evalTactic <| ← `(tactic| try rw [MLIR.run_ass_def])
--   evalTactic <| ← `(tactic| simp)

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
        | rewrite [MLIR.run_set_def]
        | rewrite [MLIR.run_if']
        | rewrite [MLIR.run_nondet]
        | rewrite [MLIR.run_eqz']
      )
      simp_op
    )
  )

elab "MLIR" : tactic => do
  evalTactic <| ← `(
    tactic| repeat MLIR_statement
  )

-- elab "MLIR_statement" : tactic => do
--   evalTactic <| ← `(
--     tactic| (
--       rewrite [MLIR.run_seq_def]
--       repeat (
--         first
--         | rewrite [MLIR.run_ass_def]
--         | rewrite [MLIR.run_set_output]
--         | rewrite [MLIR.run_if]
--         | rewrite [MLIR.run_nondet]
--         | rewrite [MLIR.run_eqz]
--       )
--       simp_op
--     )
--   )

elab "MLIR_states_simple" : tactic => do
  evalTactic <| ← `(tactic|
    simp only [
      Map.update, ite_true, Option.get!_of_some, ite_false, true_and, Option.getD_some,
      State.updateFelts, Map.fromList_cons, Map.fromList_nil, State.update_val', 
      le_refl, List.find?, List.mem_cons, ge_iff_le, tsub_eq_zero_of_le
    ])

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


-- ****************************** WEAKEST PRE - Part₀ ******************************
-- lemma is0_witness_part₀ {st : State} {y₁ y₂ : Option Felt} :
--   is0_witness st = [y₁, y₂] ↔ _ := by
--   unfold is0_witness MLIR.runProgram; simp only
--   rewrite [is0_witness_per_partes]; unfold is0_witness_program_full
--   generalize eq : (is0_witness₁; is0_witness₂; is0_witness₃; is0_witness₄; is0_witness₅) = prog
--   unfold is0_witness₀
--   MLIR
--   rewrite [←eq]
--   rfl
-- ****************************** WEAKEST PRE - Part₀ ******************************

def part₀_state (st : State) : State := 
  (st["1"] ←ₛ some (Lit.Val 1))["x"] ←ₛ
    if 0 ≤ (st["1"] ←ₛ some (Lit.Val 1)).cycle ∧
      { name := "input" } ∈ (st["1"] ←ₛ some (Lit.Val 1)).vars ∧
      0 < Map.get! (st["1"] ←ₛ some (Lit.Val 1)).bufferWidths { name := "input" } ∧
      Option.isSome (Buffer.get! (Map.get! (st["1"] ←ₛ some (Lit.Val 1)).buffers { name := "input" })
                    ((st["1"] ←ₛ some (Lit.Val 1)).cycle - Back.toNat 0, 0)) = true
    then some (Lit.Val (Option.get! (Buffer.get! (Map.get! (st["1"] ←ₛ some (Lit.Val 1)).buffers
              { name := "input" }) ((st["1"] ←ₛ some (Lit.Val 1)).cycle - Back.toNat 0, 0))))
    else none

def part₀_state_update (st : State) : State :=
  Γ (part₀_state st) ⟦is0_witness₁; is0_witness₂; is0_witness₃; is0_witness₄; is0_witness₅⟧

lemma part₀_updates {y₁ y₂ : Option Felt} (st : State) :
  (MLIR.runProgram (is0_witness₀; is0_witness₁; is0_witness₂; is0_witness₃; is0_witness₄; is0_witness₅) st).lastOutput = [y₁, y₂] ↔
  (part₀_state_update st).lastOutput = [y₁, y₂] := by
  simp only [part₀_state, part₀_state_update, MLIR.runProgram]
  unfold is0_witness₀
  MLIR

-- ****************************** WEAKEST PRE - Part₁ ******************************
-- lemma is0_witness_part₁ {y₁ y₂ : Option Felt} (st : State) :
--   let st' := MLIR.runProgram (is0_witness₁; is0_witness₂; is0_witness₃; is0_witness₄; is0_witness₅) st
--   (st'.buffers ⟨"output"⟩ |>.get!.getLast!) = [y₁, y₂] ↔ _ := by
--   unfold MLIR.runProgram; simp only
--   generalize eq : (is0_witness₂; is0_witness₃; is0_witness₄; is0_witness₅) = prog
--   unfold is0_witness₁
--   MLIR_statement
--   MLIR_statement
--   MLIR_statement
--   MLIR_statement
--   simp only [State.update_val]
--   MLIR_states_simple
--   generalize update₀ : (λ x => 
--                         if x = { name := "isZeroBit" }
--                         then some (if Option.get! (State.felts st { name := "x" }) = 0 then 1 else 0)
--                         else State.felts st x) = feltmap₀
--   generalize eq₄ : ({ buffers := st.buffers, bufferWidths := st.bufferWidths, constraints := st.constraints,
--                         cycle := st.cycle,
--                         felts := feltmap₀,
--                         isFailed := st.isFailed, props := st.props, vars := st.vars } : State) = jibadiba
--   have tit : jibadiba = State.updateFelts st "isZeroBit" (if Option.get! (State.felts st { name := "x" }) = 0 then 1 else 0) := by
--     rw [←eq₄, ←update₀]
--     congr
--   generalize eq₂ : State.set! jibadiba { name := "output" } 0
--                      (if Option.get! (State.felts st { name := "x" }) = 0 then 1 else 0) = podajiba
--   generalize update₁ : (λ x =>
--                         if x = { name := "invVal" }
--                         then some (match State.felts podajiba { name := "x" } with
--                                       | some x => if x = 0 then 0 else x⁻¹
--                                       | x => default)
--                         else State.felts podajiba x) = feltmap₁
--   generalize eq₃ :
--     ({ buffers := podajiba.buffers, bufferWidths := podajiba.bufferWidths, constraints := podajiba.constraints,
--        cycle := podajiba.cycle,
--        felts := feltmap₁,
--        isFailed := podajiba.isFailed, props := podajiba.props, vars := podajiba.vars } : State) = st₀
--   have : st₀ = State.updateFelts podajiba "invVal" (match State.felts podajiba { name := "x" } with
--                                       | some x => if x = 0 then 0 else x⁻¹
--                                       | x => default) := by
--     rw [←eq₃, ←update₁]
--     congr
--   rw [this, ←eq₂, tit]
--   rewrite [←eq]
--   rfl
-- ****************************** WEAKEST PRE - Part₁ ******************************

def part₁_state (st : State) : State :=
  State.set! (State.updateFelts (State.set! (State.updateFelts st "isZeroBit"
    (if Option.get! (State.felts st { name := "x" }) = 0 then 1 else 0))
    { name := "output" } 0 (if Option.get! (State.felts st { name := "x" }) = 0 then 1 else 0))
      "invVal"
      (match
        State.felts
          (State.set!
            (State.updateFelts st "isZeroBit"
              (if Option.get! (State.felts st { name := "x" }) = 0 then 1 else 0))
            { name := "output" } 0 (if Option.get! (State.felts st { name := "x" }) = 0 then 1 else 0))
          { name := "x" } with
      | some x => if x = 0 then 0 else x⁻¹
      | _ => default))
    { name := "output" } 1
    (match
      State.felts
        (State.set!
          (State.updateFelts st "isZeroBit"
            (if Option.get! (State.felts st { name := "x" }) = 0 then 1 else 0))
          { name := "output" } 0 (if Option.get! (State.felts st { name := "x" }) = 0 then 1 else 0))
        { name := "x" } with
    | some x => if x = 0 then 0 else x⁻¹
    | _ => default)

def part₁_state_update (st : State) : State :=
  Γ (part₁_state st) ⟦is0_witness₂; is0_witness₃; is0_witness₄; is0_witness₅⟧

lemma part₁_updates {y₁ y₂ : Option Felt} (st : State) :
  (MLIR.runProgram (is0_witness₁; is0_witness₂; is0_witness₃; is0_witness₄; is0_witness₅) st).lastOutput = [y₁, y₂] ↔
  (part₁_state_update st).lastOutput = [y₁, y₂] := by
  simp only [MLIR.runProgram]
  generalize eq : (is0_witness₂; is0_witness₃; is0_witness₄; is0_witness₅) = prog
  unfold is0_witness₁ 
  MLIR
  simp only [State.update_val', State.updateFelts, Map.update]
  unfold part₁_state_update
  aesop

lemma part₁_updates_opaque {st : State} : 
  (part₀_state_update st).lastOutput = [y₁, y₂] ↔
  (part₁_state_update (part₀_state st)).lastOutput = [y₁, y₂] := by
  simp [part₀_state_update, part₁_updates]

def part₂_state (st : State) : State :=
  st["arg1[0]"] ←ₛ 
    if 0 ≤ st.cycle ∧
      { name := "output" } ∈ st.vars ∧
      0 < Map.get! st.bufferWidths { name := "output" } ∧
      Option.isSome (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 0)) = true 
    then some (Lit.Val (Option.get! (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 0))))
    else none

def part₂_state_update (st : State) : State :=
  Γ (part₂_state st) ⟦is0_witness₃; is0_witness₄; is0_witness₅⟧

lemma part₂_updates {y₁ y₂ : Option Felt} (st : State) :
  (MLIR.runProgram (is0_witness₂; is0_witness₃; is0_witness₄; is0_witness₅) st).lastOutput = [y₁, y₂] ↔
  (part₂_state_update st).lastOutput = [y₁, y₂] := by
  simp only [part₂_state, MLIR.runProgram, part₂_state_update]
  generalize eq : (is0_witness₃; is0_witness₄; is0_witness₅) = prog
  unfold is0_witness₂
  MLIR

lemma part₂_updates_opaque {st : State} : 
  (part₁_state_update st).lastOutput = [y₁, y₂] ↔
  (part₂_state_update (part₁_state st)).lastOutput = [y₁, y₂] := by
  simp [part₁_state_update, part₂_updates]

-- ****************************** WEAKEST PRE - Part₃ ******************************
-- lemma is0_witness_part₃ {y₁ y₂ : Option Felt} (st : State) :
--   let st' := MLIR.runProgram (is0_witness₃; is0_witness₄; is0_witness₅) st
--   (st'.buffers ⟨"output"⟩ |>.get!.getLast!) = [y₁, y₂] ↔ _ := by
--   unfold MLIR.runProgram; simp only
--   generalize eq : (is0_witness₄; is0_witness₅) = prog
--   unfold is0_witness₃
--   MLIR_statement
--   rewrite [←eq]
--   rfl
-- ****************************** WEAKEST PRE - Part₃ ******************************

def part₃_state (st : State) : State :=
  if State.felts st { name := "arg1[0]" } = some 0 ∨ ¬{ name := "arg1[0]" } ∈ st.felts then st
  else if h : { name := "x" } ∈ st.felts
        then withEqZero (Option.get (State.felts st { name := "x" }) h) st
        else st

def part₃_state_update (st : State) : State :=
  Γ (part₃_state st) ⟦is0_witness₄; is0_witness₅⟧

lemma part₃_updates {y₁ y₂ : Option Felt} (st : State) :
  (MLIR.runProgram (is0_witness₃; is0_witness₄; is0_witness₅) st).lastOutput = [y₁, y₂] ↔
  (part₃_state_update st).lastOutput = [y₁, y₂] := by
  simp only [part₃_state, MLIR.runProgram, part₃_state_update]
  generalize eq : (is0_witness₄; is0_witness₅) = prog
  unfold is0_witness₃
  MLIR

lemma part₃_updates_opaque {st : State} : 
  (part₂_state_update st).lastOutput = [y₁, y₂] ↔
  (part₃_state_update (part₂_state st)).lastOutput = [y₁, y₂] := by
  simp [part₂_state_update, part₃_updates]

-- ****************************** WEAKEST PRE - Part₄ ******************************
-- lemma is0_witness_part₄ {y₁ y₂ : Option Felt} (st : State) :
--   let st' := MLIR.runProgram (is0_witness₄; is0_witness₅) st
--   (st'.buffers ⟨"output"⟩ |>.get!.getLast!) = [y₁, y₂] ↔ _ := by
--   unfold MLIR.runProgram; simp only
--   unfold is0_witness₄
--   MLIR_statement
--   rfl
-- ****************************** WEAKEST PRE - Part₄ ******************************

def part₄_state (st : State) : State :=
  st["1 - arg1[0]"] ←ₛ some (Lit.Val
    (Option.get! (State.felts st { name := "1" }) -
     Option.get! (State.felts st { name := "arg1[0]" })))

def part₄_state_update (st : State) : State :=
  Γ (part₄_state st) ⟦is0_witness₅⟧

def part₄_updates {y₁ y₂ : Option Felt} (st : State) :
  (MLIR.runProgram (is0_witness₄; is0_witness₅) st).lastOutput = [y₁, y₂] ↔
  (part₄_state_update st).lastOutput = [y₁, y₂] := by
  simp only [part₄_state, MLIR.runProgram, part₄_state_update]
  generalize eq : (is0_witness₅) = prog
  unfold is0_witness₄
  MLIR

lemma part₄_updates_opaque {st : State} : 
  (part₃_state_update st).lastOutput = [y₁, y₂] ↔
  (part₄_state_update (part₃_state st)).lastOutput = [y₁, y₂] := by
  simp [part₃_state_update, part₄_updates]

-- ****************************** WEAKEST PRE - Part₅ ******************************
-- lemma is0_witness_part₄ {y₁ y₂ : Option Felt} (st : State) :
--   let st' := MLIR.runProgram is0_witness₅ st
--   (st'.buffers ⟨"output"⟩ |>.get!.getLast!) = [y₁, y₂] ↔ _ := by
--   unfold MLIR.runProgram; simp only
--   unfold is0_witness₅
--   MLIR_statement
--   MLIR_statement
--   MLIR_statement
--   simp
--   rfl
-- ****************************** WEAKEST PRE - Part₅ ******************************

def part₅_state_update (st : State) : State :=
  if State.felts st { name := "1 - arg1[0]" } = some 0 ∨ ¬{ name := "1 - arg1[0]" } ∈ st.felts
  then st
  else st["arg1[1]"] ←ₛ
    if 0 ≤ st.cycle ∧ { name := "output" } ∈ st.vars ∧
       1 < Map.get! st.bufferWidths { name := "output" } ∧
       Option.isSome (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 1)) = true
    then some (Lit.Val (Option.get! (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 1))))
    else none

def part₅_updates {y₁ y₂ : Option Felt} (st : State) :
  (MLIR.runProgram is0_witness₅ st).lastOutput = [y₁, y₂] ↔
  (part₅_state_update st).lastOutput = [y₁, y₂] := by
  simp only [MLIR.runProgram, part₅_state_update]
  unfold is0_witness₅
  MLIR
  MLIR_states_simple
  rfl

lemma part₅_updates_opaque {st : State} : 
  (part₄_state_update st).lastOutput = [y₁, y₂] ↔
  (part₅_state_update (part₄_state st)).lastOutput = [y₁, y₂] := by
  simp [part₄_state_update, part₅_updates]

lemma is0_witness_closed_form {x : Felt} {y₁ y₂ : Option Felt} :
  is0_witness_initial x = [y₁, y₂] ↔ (.some (if x = 0 then 1 else 0)) = y₁ ∧ (if x = 0 then 0 else x⁻¹) = y₂ := by
  unfold is0_witness_initial MLIR.runProgram; simp only [is0_witness_per_partes]
  rewrite [part₀_updates]
  rewrite [part₁_updates_opaque]
  rewrite [part₂_updates_opaque]
  rewrite [part₃_updates_opaque]
  rewrite [part₄_updates_opaque]
  rewrite [part₅_updates_opaque]

  unfold is0_witness_initial_state is0_initial_state

  unfold part₀_state
  simp [State.updateFelts, Map.get!, Option.get!, Buffer.get!]

  unfold part₁_state
  simp [
    State.updateFelts, Map.get!, Option.get!, Buffer.get!,
    State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
    Option.isEqSome, List.set
  ]
  MLIR_states_simple; simp only [Map.update_def.symm]
  
  unfold part₂_state
  simp [
    State.updateFelts, Map.get!, Option.get!, Buffer.get!,
    State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
    Option.isEqSome, List.set
  ]
  MLIR_states_simple; simp only [Map.update_def.symm]

  unfold part₃_state
  simp [
    State.updateFelts, Map.get!, Option.get!, Buffer.get!,
    State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
    Option.isEqSome, List.set, Map.mem_def
  ]
  MLIR_states_simple; simp only [Map.update_def.symm]
  
  unfold part₄_state
  simp [
    State.updateFelts, Map.get!, Option.get!, Buffer.get!,
    State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
    Option.isEqSome, List.set
  ]
  MLIR_states_simple; simp only [Map.update_def.symm]
  
  unfold part₅_state_update
  simp [
    State.updateFelts, Map.get!, Option.get!, Buffer.get!,
    State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
    Option.isEqSome, List.set
  ]
  MLIR_states_simple; simp only [Map.update_def.symm]

  MLIR_states_simple; simp only [Map.update_def.symm]

  rw [State.felts_if] <;> try rfl
  simp [State.felts]
  MLIR_states_simple; simp only [Map.update_def.symm]

  rw [State.buffers_if] <;> try rfl
  simp [State.buffers]
  MLIR_states_simple; simp only [Map.update_def.symm]

  rw [State.bufferWidths_if] <;> try rfl
  simp [State.bufferWidths]
  MLIR_states_simple; simp only [Map.update_def.symm]

  rw [State.cycle_if] <;> try rfl
  simp [State.cycle]
  MLIR_states_simple; simp only [Map.update_def.symm]

  rw [State.isFailed_if] <;> try rfl
  simp [State.isFailed]
  MLIR_states_simple; simp only [Map.update_def.symm]

  rw [State.props_if] <;> try rfl
  simp [State.props]
  MLIR_states_simple; simp only [Map.update_def.symm]

  rw [State.vars_if] <;> try rfl
  simp [State.vars]
  MLIR_states_simple; simp only [Map.update_def.symm]

  simp [State.lastOutput, Option.get!, List.getLast!, List.getLast, State.buffers]
  
  rw [State.buffers_if] <;> try rfl
  simp [State.buffers]
  MLIR_states_simple; simp only [Map.update_def.symm]

  simp [List.getLast]

-- set_option maxHeartbeats 2000000 in
-- lemma is0_witness_closed_form {x y₁ y₂ : Felt} :
--   is0_witness x = [y₁, y₂] ↔ (if x = 0 then 1 else 0) = y₁ ∧ (if x = 0 then 0 else x⁻¹) = y₂ := by
--   unfold is0_witness MLIR.runProgram; simp only
--   rw [is0_witness_per_partes]
--   sorry

end Risc0
