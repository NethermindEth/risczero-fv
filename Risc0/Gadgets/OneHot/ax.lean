import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.String.Lemmas
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp

import Risc0.Basic
import Risc0.Lemmas
import Risc0.Wheels
import Risc0.MlirTactics

namespace Risc0.OneHot

open MLIRNotation

def initial_witness_state (input : Felt) : State :=
  State.empty
  |>.addBuffer "input" (Buffer.init_values [input])
  |>.addBuffer "output" (Buffer.init_unset 3)

def initial_constraint_state (input : Felt) (output : BufferAtTime) : State :=
  State.empty
  |>.addBuffer "input" (Buffer.init_values [input])
  |>.addBuffer "output" (Buffer.init' output)

def constraints (input : Felt) (output : BufferAtTime) : Prop :=
  let state' := MLIR.runProgram (st := initial_constraint_state input output) <|
  --     %0 = cirgen.const 1  
  "1" ←ₐ C 1;
  --     %1 = cirgen.const 2
  "2" ←ₐ C 2;
  --     %2 = cirgen.true
  "true" ←ₐ ⊤;
  --     %3 = cirgen.get %arg0[0] back 0 : <1, constant>
  "input" ←ₐ .Get ⟨"input"⟩ 0 0;
  --     %4 = cirgen.get %arg1[1] back 0 : <3, mutable>
  "output[1]" ←ₐ .Get ⟨"output"⟩ 0 1;
  --     %5 = cirgen.get %arg1[2] back 0 : <3, mutable>
  "output[2]" ←ₐ .Get ⟨"output"⟩ 0 2;
  --     %6 = cirgen.mul %5 : <default>, %1 : <default>
  "output[2]*2" ←ₐ .Mul ⟨"output[2]"⟩ ⟨"2"⟩;
  --     %7 = cirgen.add %4 : <default>, %6 : <default>
  "2*output[2]+output[1]" ←ₐ .Add ⟨"output[1]"⟩ ⟨"output[2]*2"⟩;
  --     %8 = cirgen.sub %7 : <default>, %3 : <default>
  "2*output[2]+output[1]-input" ←ₐ .Sub ⟨"2*output[2]+output[1]"⟩ ⟨"input"⟩;
  --     %9 = cirgen.and_eqz %2, %8 : <default>
  "andEqz 2*output[2]+output[1]-input" ←ₐ ⟨"true"⟩ &₀ ⟨"2*output[2]+output[1]-input"⟩;
  --     %10 = cirgen.get %arg1[0] back 0 : <3, mutable>
  "output[0]" ←ₐ .Get ⟨"output"⟩ 0 0;
  --     %11 = cirgen.sub %0 : <default>, %10 : <default>
  "1-Output[0]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[0]"⟩;
  --     %12 = cirgen.mul %10 : <default>, %11 : <default>
  "output[0]<=1" ←ₐ .Mul ⟨"output[0]"⟩ ⟨"1-Output[0]"⟩;
  --     %13 = cirgen.and_eqz %9, %12 : <default>
  "andEqz output[0]<=1" ←ₐ ⟨"andEqz 2*output[2]+output[1]-input"⟩ &₀ ⟨"output[0]<=1"⟩;
  --     %14 = cirgen.sub %0 : <default>, %4 : <default>
  "1-Output[1]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[1]"⟩;
  --     %15 = cirgen.mul %4 : <default>, %14 : <default>
  "output[1]<=1" ←ₐ .Mul ⟨"output[1]"⟩ ⟨"1-Output[1]"⟩;
  --     %16 = cirgen.and_eqz %13, %15 : <default>
  "andEqz output[1]<=1" ←ₐ ⟨"andEqz output[0]<=1"⟩ &₀ ⟨"output[1]<=1"⟩;
  --     %17 = cirgen.add %10 : <default>, %4 : <default>
  "output[0]+Output[1]" ←ₐ .Add ⟨"output[0]"⟩ ⟨"output[1]"⟩;
  --     %18 = cirgen.sub %0 : <default>, %5 : <default>
  "1-Output[2]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[2]"⟩;
  --     %19 = cirgen.mul %5 : <default>, %18 : <default>
  "output[2]<=1" ←ₐ .Mul ⟨"output[1]"⟩ ⟨"1-Output[1]"⟩;
  --     %20 = cirgen.and_eqz %16, %19 : <default>
  "andEqz output[2]<=1" ←ₐ ⟨"andEqz output[1]<=1"⟩ &₀ ⟨"output[2]<=1"⟩;
  --     %21 = cirgen.add %17 : <default>, %5 : <default>
  "outputSum" ←ₐ .Add ⟨"output[0]+Output[1]"⟩ ⟨"output[2]"⟩;
  --     %22 = cirgen.sub %21 : <default>, %0 : <default>
  "outputSum-1" ←ₐ .Sub ⟨"outputSum"⟩ ⟨"1"⟩;
  --     %23 = cirgen.and_eqz %20, %22 : <default>
  "andEqz outputSum-1" ←ₐ ⟨"andEqz output[2]<=1"⟩ &₀ ⟨"outputSum-1"⟩
  --     return %23 : !cirgen.constraint  
  state'.props.get! ⟨"andEqz outputSum-1"⟩


def witness_prog_full : MLIRProgram :=
  "2" ←ₐ .Const 2;
  "1" ←ₐ .Const 1;
  "0" ←ₐ .Const 0;
  "input" ←ₐ .Get ⟨"input"⟩ 0 0;
  nondet (
    "input == 0" ←ₐ ??₀⟨"input"⟩;
    ⟨"output"⟩[0] ←ᵢ ⟨"input == 0"⟩;
    "input - 1" ←ₐ .Sub ⟨"input"⟩ ⟨"1"⟩;
    "input == 1" ←ₐ ??₀⟨"input - 1"⟩;
    ⟨"output"⟩[1] ←ᵢ ⟨"input == 1"⟩;
    "input - 2" ←ₐ .Sub ⟨"input"⟩ ⟨"2"⟩;
    "input == 2" ←ₐ ??₀⟨"input - 2"⟩;
    ⟨"output"⟩[2] ←ᵢ ⟨"input == 2"⟩
  );
  "output[1]" ←ₐ .Get ⟨"output"⟩ 0 1;
  "output[2]" ←ₐ .Get ⟨"output"⟩ 0 2;
  "output[2] * 2" ←ₐ .Mul ⟨"output[2]"⟩ ⟨"2"⟩;
  "2*output[2]+output[1]" ←ₐ .Add ⟨"output[1]"⟩ ⟨"output[2] * 2"⟩;
  "2*output[2]+output[1] - input" ←ₐ .Sub ⟨"2*output[2]+output[1]"⟩ ⟨"input"⟩;
  ?₀ ⟨"2*output[2]+output[1] - input"⟩;
  "output[0]" ←ₐ .Get ⟨"output"⟩ 0 0;
  "1 - Output[0]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[0]"⟩;
  "output[0] <= 1" ←ₐ .Mul ⟨"output[0]"⟩ ⟨"1 - Output[0]"⟩;
  ?₀ ⟨"output[0] <= 1"⟩;
  "1 - Output[1]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[1]"⟩;
  "output[1] <= 1" ←ₐ .Mul ⟨"output[1]"⟩ ⟨"1 - Output[1]"⟩;
  ?₀ ⟨"output[1] <= 1"⟩;
  "output[0]AddOutput[1]" ←ₐ .Add ⟨"output[0]"⟩ ⟨"output[1]"⟩;
  "1 - Output[2]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[2]"⟩;
  "output[2] <= 1" ←ₐ .Mul ⟨"output[2]"⟩ ⟨"1 - Output[2]"⟩;
  ?₀ ⟨"output[2] <= 1"⟩;
  "outputSum" ←ₐ .Add ⟨"output[0]AddOutput[1]"⟩ ⟨"output[2]"⟩;
  "outputSum - 1" ←ₐ .Sub ⟨"outputSum"⟩ ⟨"1"⟩;
  ?₀ ⟨"outputSum - 1"⟩

def witness_prog_0_setup_recursive (n : ℕ) : MLIRProgram :=
 -- %0 = cirgen.const 2
  (match n with
  | Nat.succ n => 
      toString (Nat.succ n) ←ₐ .Const (Nat.succ n); 
      witness_prog_0_setup_recursive n
  | Nat.zero => "0" ←ₐ .Const 0)
   -- %3 = cirgen.get %arg0[0] back 0 : <1, constant>

def witness_prog_0_setup (n : ℕ) : MLIRProgram :=
  witness_prog_0_setup_recursive n;
  "input" ←ₐ .Get ⟨"input"⟩ 0 0


def witness_prog_1_nondet_inner (n : ℕ) : MLIR IsNondet.InNondet :=
   -- cirgen.nondet {
     --   %19 = cirgen.isz %3 : <default>
    match n with
    | Nat.succ n =>
      witness_prog_1_nondet_inner n;
      "input - " ++ (toString (Nat.succ n)) ←ₐ .Sub ⟨"input"⟩ ⟨toString (Nat.succ n)⟩;
      "input == " ++ (toString (Nat.succ n)) ←ₐ ??₀⟨"input - " ++ (toString (Nat.succ n))⟩;
      ⟨"output"⟩[Nat.succ n] ←ᵢ ⟨"input == " ++ (toString (Nat.succ n))⟩
    | Nat.zero =>     
      "input == 0" ←ₐ ??₀⟨"input"⟩;
      --   cirgen.set %arg1 : <3, mutable>[0] = %19 : <default>
      ⟨"output"⟩[0] ←ᵢ ⟨"input == 0"⟩

def witness_prog_1nondet (n : ℕ) : MLIRProgram := MLIR.Nondet (witness_prog_1_nondet_inner n)

def witness_prog_2_projection (n : ℕ) : MLIRProgram :=
  match n with
  | (Nat.succ Nat.zero) => "output[1]" ←ₐ .Get ⟨"output"⟩ 0 1 
  | Nat.succ n => 
      witness_prog_2_projection n;
      "output[" ++ toString n.succ ++ "]" ←ₐ .Get ⟨"output"⟩ 0 n.succ;
      "output[" ++ toString n.succ ++ "] * " ++ toString n.succ ←ₐ .Mul ⟨"output[" ++ toString n.succ ++ "]"⟩ ⟨toString n.succ⟩;
      "sum" ++ toString n.succ ←ₐ .Add ⟨"output[" ++ toString n ++ "]"⟩ ⟨"output[" ++ toString n.succ ++ "] * " ++ toString n.succ⟩
  | Nat.zero => "RIP" ←ₐ .Const 42

def witness_prog_3_sum_equals_input (n : ℕ) : MLIRProgram :=
  "sum" ++ toString n ++ " - input" ←ₐ .Sub ⟨"sum" ++ toString n⟩ ⟨"input"⟩;
  ?₀ ⟨"sum" ++ toString n ++ " - input"⟩

def witness_prog_4_output0_le_1_and_sum (n : ℕ) : MLIRProgram :=
   -- %9 = cirgen.get %arg1[0] back 0 : <3, mutable>
  match n with
  | Nat.succ n => 
    witness_prog_4_output0_le_1_and_sum n;
    -- %10 = cirgen.sub %1 : <default>, %9 : <default>
    "1 - output[" ++ toString n.succ ++ "]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[" ++ toString n.succ ++ "]"⟩;
    -- %11 = cirgen.mul %9 : <default>, %10 : <default>
    "output[" ++ toString n.succ ++ "] <= 1" ←ₐ .Mul ⟨"output[" ++ toString n.succ ++ "]"⟩ ⟨"1 - Output[" ++ toString n.succ ++ "]"⟩;
    -- cirgen.eqz %11 : <default>
    ?₀ ⟨"output[" ++ toString n.succ ++ "] <= 1"⟩;
    "output_sum[" ++ toString n.succ ++ "]" ←ₐ .Add ⟨"output_sum[" ++ toString n ++ "]"⟩ ⟨"output[" ++ toString n.succ ++ "]"⟩
  | Nat.zero => 
    "output_sum[0]" ←ₐ .Get ⟨"output"⟩ 0 0;
    -- %10 = cirgen.sub %1 : <default>, %9 : <default>
    "1 - output[0]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[0]"⟩;
    -- %11 = cirgen.mul %9 : <default>, %10 : <default>
    "output[0] <= 1" ←ₐ .Mul ⟨"output[0]"⟩ ⟨"1 - output[0]"⟩;
    -- cirgen.eqz %11 : <default>
    ?₀ ⟨"output[0] <= 1"⟩


def witness_prog_5_final_constraints (n : ℕ) : MLIRProgram :=
   -- %17 = cirgen.add %14 : <default>, %5 : <default>
   -- %18 = cirgen.sub %17 : <default>, %1 : <default>
  "outputSum - 1" ←ₐ .Sub ⟨"output_sum[" ++ toString n ++ "]"⟩ ⟨"1"⟩;
  --     cirgen.eqz %18 : <default>
  ?₀ ⟨"outputSum - 1"⟩

def part₀_state_rec (n : ℕ) (st : State) : State :=
  match n with
  | Nat.succ n => State.updateFelts (@part₀_state_rec n st) { name := toString (Nat.succ n)} (Nat.succ n)
  | Nat.zero => State.updateFelts st { name := "0"} Nat.zero

def part₀_state (n : ℕ) (st : State) : State := 
  (@part₀_state_rec n st)["input"] ←ₛ getImpl st { name := "input" } 0 0

def part₀_state_rec_update (n : ℕ) (st : State) (progr: MLIRProgram) : State :=
  Γ (@part₀_state_rec n st) ⟦progr⟧

def part₀_state_update (n : ℕ) (st : State) (progr: MLIRProgram) : State :=
  Γ (@part₀_state n st) ⟦ progr⟧

-- lemma part₀_updates {y₁ y₂ : Option Felt} (st : State) :
--   (MLIR.runProgram (witness_prog_0_setup n; witness_prog_1nondet n) st).lastOutput = [y₁, y₂] ↔
--   _ := by
--   simp only [MLIR.runProgram]
--   unfold is0_witness₀
--   MLIR

lemma toStringInj {n m : ℕ} : toString n = toString m → n = m := by sorry

lemma part₀_state_rec_comm (n m : ℕ) {x : Felt} (h : n < m) : part₀_state_rec n (st[felts][{ name := toString m }] ← x) =
  part₀_state_rec n st[felts][{ name := toString m }] ← x := by
  revert st x m
  induction' n with n ih
  · intros st m x h
    simp only [Nat.zero_eq]
    unfold part₀_state_rec
    simp only [Nat.zero_eq, Nat.cast_zero]
    unfold State.updateFelts
    simp only [State.mk.injEq, and_self, and_true, true_and]
    rw [Map.update_neq_comm]
    simp
    rcases m with _ | m 
    aesop
    have h_eq : "0" = toString Nat.zero := by simp
    rw [h_eq]
    intro contr
    have h_eq : Nat.succ m = Nat.zero := by exact (toStringInj contr)
    aesop
  · intros st m x h
    unfold part₀_state_rec
    simp only [Nat.cast_succ]
    rw [@ih st]
    rw [State.updateFelts_neq_comm]
    simp
    intro contr
    have hcontr : m = Nat.succ n := by
      {
        apply toStringInj
        exact contr
      }
    aesop
    apply Nat.lt_of_succ_lt
    exact h 

lemma part₀_updates' {n : ℕ} (st : State) :
  (MLIR.runProgram (witness_prog_0_setup_recursive n) st) =
  part₀_state_rec n st := by
  revert st
  simp only [part₀_state, part₀_state_rec_update, MLIR.runProgram]
  unfold witness_prog_0_setup_recursive
  induction' n with n ih
  · intros st
    simp
    simp only [part₀_state_rec]
    MLIR
    rfl
  · intros st
    simp only [part₀_state_rec]
    simp only [Nat.cast_succ] at ih
    MLIR
    unfold witness_prog_0_setup_recursive
    specialize (ih (st[felts][{ name := toString (Nat.succ n) }] ← ↑n + 1))
    simp
    rw [ih]
    rw [part₀_state_rec_comm]
    aesop

lemma getImpl_safe : getImpl (Γ st ⟦witness_prog_0_setup_recursive n⟧) { name := "input" } 0 0 = getImpl st { name := "input" } 0 0 := by
  revert st
  unfold witness_prog_0_setup_recursive
  induction' n with n ih
  · intros st
    simp [getImpl, isGetValid]
    MLIR_states
  · intros st
    MLIR
    rw [ih]
    simp [getImpl, isGetValid]
    MLIR_states

lemma part₀_updates {output : BufferAtTime} {n : ℕ} (st : State) :
  (MLIR.runProgram (witness_prog_0_setup n; witness_prog_1nondet n; witness_prog_2_projection n; witness_prog_3_sum_equals_input n; witness_prog_4_output0_le_1_and_sum n; witness_prog_5_final_constraints n) st).lastOutput = output ↔
  (part₀_state_update n st (witness_prog_1nondet n; witness_prog_2_projection n; witness_prog_3_sum_equals_input n; witness_prog_4_output0_le_1_and_sum n; witness_prog_5_final_constraints n)).lastOutput = output := by
  simp only [part₀_state, part₀_state_update, MLIR.runProgram]
  generalize eq : (witness_prog_1nondet n; witness_prog_2_projection n; witness_prog_3_sum_equals_input n; witness_prog_4_output0_le_1_and_sum n; witness_prog_5_final_constraints n) = progr
  unfold witness_prog_0_setup
  MLIR
  rw [←@part₀_updates' n st, getImpl_safe]

-- def witness_prog_1_nondet_inner (n : ℕ) : MLIR IsNondet.InNondet :=
--    -- cirgen.nondet {
--      --   %19 = cirgen.isz %3 : <default>
--     match n with
--     | Nat.succ n =>
--       witness_prog_1_nondet_inner n;
--       "input - " ++ (toString (Nat.succ n)) ←ₐ .Sub ⟨"input"⟩ ⟨toString (Nat.succ n)⟩;
--       "input == " ++ (toString (Nat.succ n)) ←ₐ ??₀⟨"input - " ++ (toString (Nat.succ n))⟩;
--       ⟨"output"⟩[Nat.succ n] ←ᵢ ⟨"input == " ++ (toString (Nat.succ n))⟩
--     | Nat.zero =>     
--       "input == 0" ←ₐ ??₀⟨"input"⟩;
--       --   cirgen.set %arg1 : <3, mutable>[0] = %19 : <default>
--       ⟨"output"⟩[0] ←ᵢ ⟨"input == 0"⟩

def part₁_state (n : ℕ) (st : State) : State :=
  match n with
  | Nat.succ n => State.set! ((@part₁_state n st[felts][⟨"input - " ++ toString (Nat.succ n)⟩] ← (st.felts ⟨"input"⟩).get! - (st.felts ⟨toString n.succ⟩).get!)[felts][⟨"input == " ++ (toString (Nat.succ n))⟩] ← (if (st.felts ⟨"input"⟩).get! = Nat.succ n then 1 else 0)) ⟨"output"⟩ n.succ (if (st.felts ⟨"input"⟩).get! = Nat.succ n then 1 else 0)
  | Nat.zero => State.set! (st[felts][⟨"input == 0"⟩] ← if (st.felts ⟨"input"⟩).get! = 0 then 1 else 0) ⟨"output"⟩ 0 (if (st.felts ⟨"input"⟩).get! = 0 then 1 else 0)

def part₁_state_update (n : ℕ) (st : State) (progr: MLIRProgram) : State :=
  Γ (@part₁_state n st) ⟦progr⟧

lemma input_toString {n : ℕ} : ¬"input - " ++ toString n = "input" := by
  intros contr
  have h : ("input - " ++ toString n).length = "input".length := by rw [contr]
  rw [String.length_append] at h
  simp [String.length] at h
  rw [Nat.succ_add] at h
  rw [Nat.succ_add] at h
  rw [Nat.succ_add] at h
  rw [Nat.succ_add] at h
  rw [Nat.succ_add] at h
  rw [Nat.succ_add] at h
  aesop
  
lemma input_toString' {n : ℕ} : ¬"input == " ++ toString n = "input" := by
  intros contr
  have h : ("input == " ++ toString n).length = "input".length := by rw [contr]
  rw [String.length_append] at h
  simp [String.length] at h
  rw [Nat.succ_add] at h
  rw [Nat.succ_add] at h
  rw [Nat.succ_add] at h
  rw [Nat.succ_add] at h
  rw [Nat.succ_add] at h
  rw [Nat.succ_add] at h
  aesop

lemma part₁_doesnt_touch_input {n : ℕ} {st : State} : State.felts (part₁_state n st) { name := "input" } = State.felts st { name := "input" } := by
  revert st
  induction' n with n ih
  · intros st
    unfold part₁_state
    simp
    rw [←@Map.getElem_def _ _ (st.felts[{ name := "input == 0" }] ←ₘ if Option.get! (State.felts st { name := "input" }) = 0 then 1 else 0), Map.update_get_next]
    rfl
    aesop
  · intros st
    unfold part₁_state
    simp
    rw [←@Map.getElem_def _ _ (((part₁_state n st).felts[{ name := "input - " ++ toString (Nat.succ n) }] ←ₘ
        Option.get! (State.felts st { name := "input" }) -
          Option.get!
            (State.felts st { name := toString (Nat.succ n) }))[{ name := "input == " ++ toString (Nat.succ n) }] ←ₘ
      if Option.get! (State.felts st { name := "input" }) = ↑n + 1 then 1 else 0), Map.update_get_next, Map.update_get_next]
    specialize (@ih st)
    rw [Map.getElem_def, ih]
    simp
    exact input_toString
    simp
    exact input_toString'

lemma part₁_doesnt_touch_n_succ {n : ℕ} {st : State} : State.felts (part₁_state n st) { name := toString n.succ } = State.felts st { name := toString n.succ } := by 
  
  -- revert st
  -- induction' n with n ih
  -- · intros st
  --   unfold part₁_state
  --   simp
  --   rw [←@Map.getElem_def _ _ (st.felts[{ name := "input == 0" }] ←ₘ if Option.get! (State.felts st { name := "input" }) = 0 then 1 else 0), Map.update_get_next]
  --   rfl
  --   aesop
  -- · intros st
  --   unfold part₁_state
  --   simp
  --   rw [←@Map.getElem_def _ _ (((part₁_state n st).felts[{ name := "input - " ++ toString (Nat.succ n) }] ←ₘ
  --       Option.get! (State.felts st { name := "input" }) -
  --         Option.get!
  --           (State.felts st { name := toString (Nat.succ n) }))[{ name := "input == " ++ toString (Nat.succ n) }] ←ₘ
  --     if Option.get! (State.felts st { name := "input" }) = ↑n + 1 then 1 else 0), Map.update_get_next, Map.update_get_next]
  --   specialize (@ih st)
  --   rw [Map.getElem_def, ih]
  --   simp
  --   exact input_toString
  --   simp
  --   exact input_toString'

lemma part₁_updates' {n : ℕ} (st : State) :
  (MLIR.run (witness_prog_1_nondet_inner n) st) = part₁_state n st := by
  revert st
  induction' n with n ih
  · unfold witness_prog_1_nondet_inner
    intros st
    MLIR
    rfl
  · intros st
    unfold part₁_state witness_prog_1_nondet_inner
    simp
    MLIR
    rw [ih, part₁_doesnt_touch_input]
    simp

    by_cases 
    rw [←ih]
    simp only [Nat.cast_succ]
    simp [State.set!]
    simp [State.setBufferElementImpl]
    



lemma part₁_updates {output : BufferAtTime} {n : ℕ} (st : State) :
  (MLIR.runProgram (witness_prog_1nondet n; witness_prog_2_projection n; witness_prog_3_sum_equals_input n; witness_prog_4_output0_le_1_and_sum n; witness_prog_5_final_constraints n) st).lastOutput = output ↔
  (part₀_state_update n st (witness_prog_2_projection n; witness_prog_3_sum_equals_input n; witness_prog_4_output0_le_1_and_sum n; witness_prog_5_final_constraints n)).lastOutput = output := by
  simp only [part₀_state, part₀_state_update, MLIR.runProgram]
  generalize eq : (witness_prog_1nondet n; witness_prog_2_projection n; witness_prog_3_sum_equals_input n; witness_prog_4_output0_le_1_and_sum n; witness_prog_5_final_constraints n) = progr
  unfold witness_prog_0_setup
  MLIR
  rw [←@part₀_updates' n st, getImpl_safe]

def witness (input : Felt) : BufferAtTime :=
  witness_prog_full.run (initial_witness_state input)
  |>.buffers.get! ⟨"output"⟩
  |>.last!

def constraints_prog_0_setup_recursive (n : ℕ) : MLIRProgram :=
  (match n with
  | Nat.succ n => 
      witness_prog_0_setup_recursive n;
      toString (Nat.succ n) ←ₐ .Const (Nat.succ n)
  | Nat.zero => "0" ←ₐ .Const 0)

def constraints_prog_0_setup (n : ℕ) : MLIRProgram :=
  constraints_prog_0_setup_recursive n;
  "true"      ←ₐ ⊤;
  "input" ←ₐ .Get ⟨"input"⟩ 0 0

def constraints_prog_1_projection (n : ℕ) : MLIRProgram :=
  match n with
  | (Nat.succ Nat.zero) => "output[1]" ←ₐ .Get ⟨"output"⟩ 0 1 
  | Nat.succ n => 
      "output[" ++ toString n.succ ++ "]" ←ₐ .Get ⟨"output"⟩ 0 n.succ;
      "output[" ++ toString n.succ ++ "] * " ++ toString n.succ ←ₐ .Mul ⟨"output[" ++ toString n.succ ++ "]"⟩ ⟨toString n.succ⟩;
      "sum" ++ toString n.succ ←ₐ .Add ⟨"output[" ++ toString n ++ "]"⟩ ⟨"output[" ++ toString n.succ ++ "] * " ++ toString n.succ⟩;
      constraints_prog_1_projection n
  | Nat.zero => "RIP" ←ₐ .Const 42

def constraints_prog_3_sum_equals_input (n : ℕ) : MLIRProgram :=
  "sum" ++ toString n ++ " - input" ←ₐ .Sub ⟨"sum" ++ toString n⟩ ⟨"input"⟩;
  "andEqzSumInput" ←ₐ ⟨"true"⟩ &₀ ⟨"sum" ++ toString n ++ " - input"⟩ 

def constraints_prog_4_output0_le_1_and_sum (n : ℕ) : MLIRProgram :=
   -- %9 = cirgen.get %arg1[0] back 0 : <3, mutable>
  match n with
  | Nat.succ n => 
    -- %10 = cirgen.sub %1 : <default>, %9 : <default>
    "1 - output[" ++ toString n.succ ++ "]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[" ++ toString n.succ ++ "]"⟩;
    -- %11 = cirgen.mul %9 : <default>, %10 : <default>
    "output[" ++ toString n.succ ++ "] <= 1" ←ₐ .Mul ⟨"output[" ++ toString n.succ ++ "]"⟩ ⟨"1 - Output[" ++ toString n.succ ++ "]"⟩;
    -- cirgen.eqz %11 : <default>
    "andEqzNonZero[" ++ toString n.succ ++ "]" ←ₐ ⟨"andEqzNonZero[" ++ toString n ++ "]"⟩ &₀ ⟨"output[" ++ toString n.succ ++ "] <= 1"⟩;
    constraints_prog_4_output0_le_1_and_sum n
  | Nat.zero => 
    "output_sum[0]" ←ₐ .Get ⟨"output"⟩ 0 0;
    -- %10 = cirgen.sub %1 : <default>, %9 : <default>
    "1 - output[0]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[0]"⟩;
    -- %11 = cirgen.mul %9 : <default>, %10 : <default>
    "output[0] <= 1" ←ₐ .Mul ⟨"output[0]"⟩ ⟨"1 - output[0]"⟩;
    -- cirgen.eqz %11 : <default>
    "andEqzNonZero[0]" ←ₐ ⟨"andEqzSumInput"⟩ &₀ ⟨"output[" ++ toString n.succ ++ "] <= 1"⟩



def kronecker (i : ℕ) (j : ℕ) : ℕ := if i = j then 1 else 0

def ith_hot (n : ℕ) (i : ℕ) : BufferAtTime :=
  ((List.range n).tail.map (kronecker i)).map some

lemma constraints_closed_form {input : Felt} {output: BufferAtTime} :
  constraints input output ↔ ∃ (i : ℕ), i <= n → input = i ∧  output = ith_hot n i := by
  sorry

lemma witness_closed_form {input : Felt} {output : BufferAtTime} :
  witness input = output ↔ (
    input = 0 ∧ output = [1,0,0].map some ∨
    input = 1 ∧ output = [0,1,0].map some ∨
    input = 2 ∧ output = [0,0,1].map some
  ) := by
  sorry

theorem witness_implies_constraints {input : Felt} {output : BufferAtTime} :
  witness input = output → constraints input output := by
  simp [constraints_closed_form, witness_closed_form]

end Risc0.OneHot
