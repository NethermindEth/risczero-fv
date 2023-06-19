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

abbrev is0_constraints_prog_return := "if other cond"

def is0_constraints_prog : MLIRProgram :=
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
  is0_constraints_prog_return ←ₐ guard ⟨"1 - out[0]"⟩ & ⟨"if out[0] then eqz x"⟩ with ⟨"other cond"⟩ 

def is0_constraints (st : State) : BufferAtTime := 
  is0_constraints_prog.runProgram st |>.lastOutput

abbrev State.is0ConstraintsProps (st : State) := st |>.constraintsInVar ⟨is0_constraints_prog_return⟩

def is0_constraints_initial (input : Felt) (output : List (Option Felt)) : Prop :=
  is0_constraints_prog.runProgram (is0_initial_state input output) |>.is0ConstraintsProps

def is0_constraints₀ : MLIRProgram :=
  "1"         ←ₐ C 1; 
  "0"         ←ₐ C 0;
  -- %1 = cirgen.true
  "true"      ←ₐ ⊤ 

def is0_constraints₁ : MLIRProgram :=
  -- %2 = cirgen.get %arg0[0] back 0 : <1, constant>
  "x"         ←ₐ .Get ⟨"input"⟩ 0 0;
  -- %3 = cirgen.get %arg1[0] back 0 : <2, mutable>
  "out[0]"    ←ₐ .Get ⟨"output"⟩ 0 0;
  -- %4 = cirgen.and_eqz %1, %2 : <default>
  "andEqz x"  ←ₐ ⟨"true"⟩ &₀ ⟨"x"⟩

def is0_constraints₂ : MLIRProgram :=
  -- %5 = cirgen.and_cond %1, %3 : <default>, %4
  "if out[0] then eqz x" ←ₐ guard ⟨"out[0]"⟩ & ⟨"true"⟩ with ⟨"andEqz x"⟩;  
  -- %6 = cirgen.sub %0 : <default>, %3 : <default>
  "1 - out[0]" ←ₐ Op.Sub ⟨"1"⟩ ⟨"out[0]"⟩;
  -- %7 = cirgen.get %arg1[1] back 0 : <2, mutable>
  "out[1]"         ←ₐ .Get ⟨"output"⟩ 0 1

def is0_constraints₃ : MLIRProgram :=
  -- %8 = cirgen.mul %2 : <default>, %7 : <default>
  "x * out[1]"     ←ₐ Op.Mul ⟨"x"⟩ ⟨"out[1]"⟩; 
  -- %9 = cirgen.sub %8 : <default>, %0 : <default>
  "x * out[1] - 1" ←ₐ Op.Sub ⟨"x * out[1]"⟩ ⟨"1"⟩;
  -- %10 = cirgen.and_eqz %1, %9 : <default>
  "other cond" ←ₐ ⟨"true"⟩ &₀ ⟨"x * out[1] - 1"⟩

def is0_constraints₄ : MLIRProgram :=
  -- %11 = cirgen.and_cond %5, %6 : <default>, %10
  "if other cond" ←ₐ guard ⟨"1 - out[0]"⟩ & ⟨"if out[0] then eqz x"⟩ with ⟨"other cond"⟩

abbrev is0_constraints_program_full : MLIRProgram :=
  is0_constraints₀; is0_constraints₁; is0_constraints₂; is0_constraints₃; is0_constraints₄

lemma is0_constraints_per_partes {st : State} :
  Γ st ⟦is0_constraints_prog⟧ =
  Γ st ⟦is0_constraints_program_full⟧ := by 
  unfold is0_constraints_program_full
         is0_constraints_prog
         is0_constraints₀
         is0_constraints₁
         is0_constraints₂
         is0_constraints₃
         is0_constraints₄
  simp [MLIR.run_seq_def] -- Lazy :)  

lemma is0_constraints_per_partes_initial {input} :
  Γ (is0_witness_initial_state input) ⟦is0_constraints_prog⟧ =
  Γ (is0_witness_initial_state input) ⟦is0_constraints_program_full⟧ :=
  is0_constraints_per_partes

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
  (State.updateFelts st { name := "1" } 1)["x"] ←ₛ getImpl st { name := "input" } 0 0

def part₀_state_update (st : State) : State :=
  Γ (part₀_state st) ⟦is0_witness₁; is0_witness₂; is0_witness₃; is0_witness₄; is0_witness₅⟧

lemma part₀_updates {y₁ y₂ : Option Felt} (st : State) :
  (MLIR.runProgram (is0_witness₀; is0_witness₁; is0_witness₂; is0_witness₃; is0_witness₄; is0_witness₅) st).lastOutput = [y₁, y₂] ↔
  (part₀_state_update st).lastOutput = [y₁, y₂] := by
  simp only [part₀_state, part₀_state_update, MLIR.runProgram]
  unfold is0_witness₀
  MLIR

-- example {st : State} {x : Felt} : (st["isZeroBit"] ←ₛ Option.some (.Val x)).felts {name := "isZeroBit"} = _ := by

-- ****************************** WEAKEST PRE - Part₁ ******************************
-- lemma is0_witness_part₁ {y₁ y₂ : Option Felt} (st : State) :
--   let st' := MLIR.runProgram (is0_witness₁; is0_witness₂; is0_witness₃; is0_witness₄; is0_witness₅) st
--   (st'.buffers ⟨"output"⟩ |>.get!.getLast!) = [y₁, y₂] ↔ _ := by
--   unfold MLIR.runProgram; simp only
--   generalize eq : (is0_witness₂; is0_witness₃; is0_witness₄; is0_witness₅) = prog
--   unfold is0_witness₁
--   MLIR
--   rewrite [←eq]
--   rfl
-- ****************************** WEAKEST PRE - Part₁ ******************************

def part₁_state (st : State) : State :=
  State.set! (State.updateFelts (State.set! (State.updateFelts st
    { name := "isZeroBit" }
    (if Option.get! (State.felts st { name := "x" }) = 0 then 1 else 0)) { name := "output" } 0
    (if Option.get! (State.felts st { name := "x" }) = 0 then 1 else 0)) { name := "invVal" }
    (if Option.get! st.felts[({ name := "x" } : FeltVar)]! = 0 then 0 else (Option.get! st.felts[({ name := "x" } : FeltVar)]!)⁻¹)) { name := "output" } 1
    (if Option.get! st.felts[({ name := "x" } : FeltVar)]! = 0 then 0 else (Option.get! st.felts[({ name := "x" } : FeltVar)]!)⁻¹)

def part₁_state_update (st : State) : State :=
  Γ (part₁_state st) ⟦is0_witness₂; is0_witness₃; is0_witness₄; is0_witness₅⟧

lemma part₁_updates {y₁ y₂ : Option Felt} (st : State) :
  (MLIR.runProgram (is0_witness₁; is0_witness₂; is0_witness₃; is0_witness₄; is0_witness₅) st).lastOutput = [y₁, y₂] ↔
  (part₁_state_update st).lastOutput = [y₁, y₂] := by
  simp only [MLIR.runProgram, part₁_state_update]
  generalize eq : (is0_witness₂; is0_witness₃; is0_witness₄; is0_witness₅) = prog
  unfold is0_witness₁ 
  MLIR
  rfl

lemma part₁_updates_opaque {st : State} : 
  (part₀_state_update st).lastOutput = [y₁, y₂] ↔
  (part₁_state_update (part₀_state st)).lastOutput = [y₁, y₂] := by
  simp [part₀_state_update, part₁_updates]

def part₂_state (st : State) : State :=
  st["arg1[0]"] ←ₛ getImpl st { name := "output" } 0 0

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
  if Option.get! st.felts[({ name := "arg1[0]" } : FeltVar)]! = 0
  then st
  else withEqZero (Option.get! st.felts[({ name := "x" } : FeltVar)]!) st

def part₃_state_update (st : State) : State :=
  Γ (part₃_state st) ⟦is0_witness₄; is0_witness₅⟧

lemma part₃_updates {y₁ y₂ : Option Felt} (st : State) :
  (MLIR.runProgram (is0_witness₃; is0_witness₄; is0_witness₅) st).lastOutput = [y₁, y₂] ↔
  (part₃_state_update st).lastOutput = [y₁, y₂] := by
  unfold part₃_state_update part₃_state MLIR.runProgram
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
-- lemma is0_witness_part₅ {y₁ y₂ : Option Felt} (st : State) :
--   let st' := MLIR.runProgram is0_witness₅ st
--   (st'.buffers ⟨"output"⟩ |>.get!.getLast!) = [y₁, y₂] ↔ _ := by
--   unfold MLIR.runProgram; simp only
--   unfold is0_witness₅
--   MLIR
--   simp [State.updateFelts]
--   rfl
-- ****************************** WEAKEST PRE - Part₅ ******************************

def part₅_state_update (st : State) : State :=
  if Option.get! st.felts[({ name := "1 - arg1[0]" } : FeltVar)]! = 0
  then st
  else st["arg1[1]"] ←ₛ getImpl st { name := "output" } 0 1

def part₅_updates {y₁ y₂ : Option Felt} (st : State) :
  (MLIR.runProgram is0_witness₅ st).lastOutput = [y₁, y₂] ↔
  (part₅_state_update st).lastOutput = [y₁, y₂] := by
  simp only [MLIR.runProgram, part₅_state_update]
  unfold is0_witness₅
  MLIR
  aesop

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
  MLIR_states_updates

  unfold part₁_state
  MLIR_states_updates

  unfold part₂_state
  MLIR_states_updates

  unfold part₃_state
  MLIR_states_updates

  unfold part₄_state
  MLIR_states_updates

  unfold part₅_state_update
  MLIR_states_updates

  simp [State.lastOutput, Option.get!, List.getLast!, List.getLast, State.buffers]
  MLIR_states_updates
  simp [List.getLast]

namespace constraints

-- ****************************** WEAKEST PRE - Part₀ ******************************
-- lemma is0_witness_part₀ {st : State} {y₁ y₂ : Option Felt} :
--   is0_constraints st = [y₁, y₂] ↔ _ := by
--   unfold is0_constraints MLIR.runProgram; simp only
--   rewrite [is0_constraints_per_partes]; unfold is0_constraints_program_full
--   generalize eq : (is0_constraints₁; is0_constraints₂; is0_constraints₃; is0_constraints₄) = prog
--   unfold is0_constraints₀
--   MLIR
--   rewrite [←eq]
--   rfl
-- ****************************** WEAKEST PRE - Part₀ ******************************

def part₀_state (st : State) : State :=
  ((st["1"] ←ₛ some (Lit.Val 1))["0"] ←ₛ some (Lit.Val 0))["true"] ←ₛ some (Lit.Constraint True)

def part₀_state_update (st : State) : State :=
  Γ (part₀_state st) ⟦is0_constraints₁; is0_constraints₂; is0_constraints₃; is0_constraints₄⟧

lemma part₀_updates {st : State} :
  (MLIR.runProgram (is0_constraints₀; is0_constraints₁; is0_constraints₂; is0_constraints₃; is0_constraints₄) st).is0ConstraintsProps ↔
  (part₀_state_update st).is0ConstraintsProps := by
  simp only [part₀_state, part₀_state_update, MLIR.runProgram]
  unfold is0_constraints₀
  MLIR

-- ****************************** WEAKEST PRE - Part₁ ******************************
-- lemma is0_witness_part₁ {st : State} {y₁ y₂ : Option Felt} :
--   let st' := MLIR.runProgram (is0_constraints₁; is0_constraints₂; is0_constraints₃; is0_constraints₄) st
--   st'.is0ConstraintsProps ↔ _ := by
--   unfold MLIR.runProgram; simp only
--   generalize eq : (is0_constraints₂; is0_constraints₃; is0_constraints₄) = prog
--   unfold is0_constraints₁
--   MLIR
--   rewrite [←eq]
--   simp
--   rfl
-- ****************************** WEAKEST PRE - Part₁ ******************************

def part₁_state (st : State) : State :=
  ((st["x"] ←ₛ getImpl st { name := "input" } 0 0)["out[0]"] ←ₛ
          getImpl (st["x"] ←ₛ getImpl st { name := "input" } 0 0) { name := "output" } 0 0)["andEqz x"] ←ₛ
        some
          (Lit.Constraint
            (Option.get!
                (State.props
                  ((st["x"] ←ₛ getImpl st { name := "input" } 0 0)["out[0]"] ←ₛ
                    getImpl (st["x"] ←ₛ getImpl st { name := "input" } 0 0) { name := "output" } 0 0)
                  { name := "true" }) ∧
              Option.get!
                  (State.felts
                    ((st["x"] ←ₛ getImpl st { name := "input" } 0 0)["out[0]"] ←ₛ
                      getImpl (st["x"] ←ₛ getImpl st { name := "input" } 0 0) { name := "output" } 0 0)
                    { name := "x" }) =
                0))

def part₁_state_update (st : State) : State :=
  Γ (part₁_state st) ⟦is0_constraints₂; is0_constraints₃; is0_constraints₄⟧

lemma part₁_updates {st : State} :
  (MLIR.runProgram (is0_constraints₁; is0_constraints₂; is0_constraints₃; is0_constraints₄) st).is0ConstraintsProps ↔
  (part₁_state_update st).is0ConstraintsProps := by
  simp only [part₁_state, part₁_state_update, MLIR.runProgram]
  unfold is0_constraints₁
  MLIR
  
lemma part₁_updates_opaque {st : State} : 
  (part₀_state_update st).is0ConstraintsProps ↔
  (part₁_state_update (part₀_state st)).is0ConstraintsProps := by
  simp [part₀_state_update, part₁_updates]

-- ****************************** WEAKEST PRE - Part₂ ******************************
-- lemma is0_witness_part₂ {st : State} {y₁ y₂ : Option Felt} :
--   is0_constraints st = [y₁, y₂] ↔ _ := by
--   unfold is0_constraints MLIR.runProgram; simp only
--   rewrite [is0_constraints_per_partes]; unfold is0_constraints_program_full
--   generalize eq : (is0_constraints₁; is0_constraints₂; is0_constraints₃; is0_constraints₄) = prog
--   unfold is0_constraints₀
--   MLIR
--   rewrite [←eq]
--   rfl
-- ****************************** WEAKEST PRE - Part₂ ******************************

def part₂_state (st : State) : State :=
  (State.updateFelts
  (st["if out[0] then eqz x"] ←ₛ
    some
      (Lit.Constraint
        (Option.get! (State.props st { name := "true" }) ∧
          if Option.get! (State.felts st { name := "out[0]" }) = 0 then True
          else Option.get! (State.props st { name := "andEqz x" }))))
  { name := "1 - out[0]" }
  (Option.get! (State.felts st { name := "1" }) -
   Option.get! (State.felts st { name := "out[0]" })))["out[1]"] ←ₛ getImpl st { name := "output" } 0 1

def part₂_state_update (st : State) : State :=
  Γ (part₂_state st) ⟦is0_constraints₃; is0_constraints₄⟧

lemma part₂_updates {st : State} :
  (MLIR.runProgram (is0_constraints₂; is0_constraints₃; is0_constraints₄) st).is0ConstraintsProps ↔
  (part₂_state_update st).is0ConstraintsProps := by
  simp only [MLIR.runProgram, part₂_state_update, part₂_state]
  unfold is0_constraints₂
  MLIR
  
lemma part₂_updates_opaque {st : State} : 
  (part₁_state_update st).is0ConstraintsProps ↔
  (part₂_state_update (part₁_state st)).is0ConstraintsProps := by
  simp [part₁_state_update, part₂_updates]

-- ****************************** WEAKEST PRE - Part₃ ******************************
-- lemma is0_witness_part₀ {st : State} {y₁ y₂ : Option Felt} :
--   is0_constraints st = [y₁, y₂] ↔ _ := by
--   unfold is0_constraints MLIR.runProgram; simp only
--   rewrite [is0_constraints_per_partes]; unfold is0_constraints_program_full
--   generalize eq : (is0_constraints₁; is0_constraints₂; is0_constraints₃; is0_constraints₄) = prog
--   unfold is0_constraints₀
--   MLIR
--   rewrite [←eq]
--   rfl
-- ****************************** WEAKEST PRE - Part₃ ******************************

def part₃_state (st : State) : State :=
  (State.updateFelts
          (State.updateFelts st { name := "x * out[1]" }
            (Option.get! (State.felts st { name := "x" }) * Option.get! (State.felts st { name := "out[1]" })))
          { name := "x * out[1] - 1" }
          (Option.get! (State.felts st { name := "x" }) * Option.get! (State.felts st { name := "out[1]" }) -
            Option.get!
              (State.felts
                (State.updateFelts st { name := "x * out[1]" }
                  (Option.get! (State.felts st { name := "x" }) * Option.get! (State.felts st { name := "out[1]" })))
                { name := "1" })))["other cond"] ←ₛ
        some
          (Lit.Constraint
            (Option.get! (State.props st { name := "true" }) ∧
              Option.get! (State.felts st { name := "x" }) * Option.get! (State.felts st { name := "out[1]" }) -
                  Option.get!
                    (State.felts
                      (State.updateFelts st { name := "x * out[1]" }
                        (Option.get! (State.felts st { name := "x" }) *
                          Option.get! (State.felts st { name := "out[1]" })))
                      { name := "1" }) =
                0))

def part₃_state_update (st : State) : State :=
  Γ (part₃_state st) ⟦is0_constraints₄⟧

lemma part₃_updates {st : State} :
  (MLIR.runProgram (is0_constraints₃; is0_constraints₄) st).is0ConstraintsProps ↔
  (part₃_state_update st).is0ConstraintsProps := by
  simp only [MLIR.runProgram, part₃_state_update, part₃_state]
  unfold is0_constraints₃
  MLIR

lemma part₃_updates_opaque {st : State} : 
  (part₂_state_update st).is0ConstraintsProps ↔
  (part₃_state_update (part₂_state st)).is0ConstraintsProps := by
  simp [part₂_state_update, part₃_updates]

-- ****************************** WEAKEST PRE - Part₄ ******************************
-- lemma is0_witness_part₀ {st : State} {y₁ y₂ : Option Felt} :
--   is0_constraints st = [y₁, y₂] ↔ _ := by
--   unfold is0_constraints MLIR.runProgram; simp only
--   rewrite [is0_constraints_per_partes]; unfold is0_constraints_program_full
--   generalize eq : (is0_constraints₁; is0_constraints₂; is0_constraints₃; is0_constraints₄) = prog
--   unfold is0_constraints₀
--   MLIR
--   rewrite [←eq]
--   rfl
-- ****************************** WEAKEST PRE - Part₄ ******************************

def part₄_state_update (st : State) : State := 
  st["if other cond"] ←ₛ
      some
        (Lit.Constraint
          (Option.get! (State.props st { name := "if out[0] then eqz x" }) ∧
            if Option.get! (State.felts st { name := "1 - out[0]" }) = 0 then True
            else Option.get! (State.props st { name := "other cond" })))

lemma part₄_updates {st : State} :
  (MLIR.runProgram (is0_constraints₄) st).is0ConstraintsProps ↔
  (part₄_state_update st).is0ConstraintsProps := by
  simp only [MLIR.runProgram, part₄_state_update, part₄_state]
  unfold is0_constraints₄
  rw [MLIR.run_ass_def]
  MLIR

lemma part₄_updates_opaque {st : State} : 
  (part₃_state_update st).is0ConstraintsProps ↔
  (part₄_state_update (part₃_state st)).is0ConstraintsProps := by
  simp [part₃_state_update, part₄_updates]

lemma is0_constraints_closed_form {x: Felt} {y₁ y₂ : Felt} :
    is0_constraints_initial x ([some y₁, some y₂]) ↔
    (if 1 - y₁ = 0 then if y₁ = 0 then True else x = 0 else (if y₁ = 0 then True else x = 0) ∧ x * y₂ - 1 = 0) := by    
  unfold is0_constraints_initial MLIR.runProgram; simp only [is0_constraints_per_partes]
  rw [part₀_updates]
  rw [part₁_updates_opaque]
  rw [part₂_updates_opaque]
  rw [part₃_updates_opaque]
  rw [part₄_updates_opaque]

  generalize eq : if 1 - y₁ = 0 then if y₁ = 0 then True else x = 0 else (if y₁ = 0 then True else x = 0) ∧ x * y₂ - 1 = 0 = rhs

  unfold is0_initial_state

  unfold part₀_state
  MLIR_states_updates

  unfold part₁_state
  MLIR_states_updates
  
  unfold part₂_state
  MLIR_states_updates

  unfold part₃_state
  MLIR_states_updates

  unfold part₄_state_update
  MLIR_states_updates

  simp [State.is0ConstraintsProps, State.constraintsInVar, State.constraints]
  rw [←eq]
  
  

end constraints

end Risc0
