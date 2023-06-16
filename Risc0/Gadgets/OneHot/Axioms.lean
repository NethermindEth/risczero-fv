import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp

import Risc0.Basic
import Risc0.Lemmas
import Risc0.Wheels

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

def witness_prog_0_setup (n : ℕ) : MLIRProgram :=
 -- %0 = cirgen.const 2
  (match n with
  | Nat.succ n => 
      toString (Nat.succ n) ←ₐ .Const (Nat.succ n); 
      witness_prog_0_setup n
  | Nat.zero => "0" ←ₐ .Const 0);
   -- %3 = cirgen.get %arg0[0] back 0 : <1, constant>
  "input" ←ₐ .Get ⟨"input"⟩ 0 0


def witness_prog_1_nondet_inner (n : ℕ) : MLIR IsNondet.InNondet :=
   -- cirgen.nondet {
     --   %19 = cirgen.isz %3 : <default>
    match n with
    | Nat.succ n =>
      witness_prog_1_nondet_inner n;
      "input - " ++ (toString (Nat.succ n)) ←ₐ .Sub ⟨"input"⟩ ⟨toString (Nat.succ n)⟩;
      "input == " ++ (toString (Nat.succ n)) ←ₐ ??₀⟨"input"⟩;
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


def witness_prog_4_final_constraints (n : ℕ) : MLIRProgram :=
   -- %17 = cirgen.add %14 : <default>, %5 : <default>
   -- %18 = cirgen.sub %17 : <default>, %1 : <default>
  "outputSum - 1" ←ₐ .Sub ⟨"output_sum[" ++ toString n ++ "]"⟩ ⟨"1"⟩;
  --     cirgen.eqz %18 : <default>
  ?₀ ⟨"outputSum - 1"⟩

def witness (input : Felt) : BufferAtTime :=
  witness_prog_full.run (initial_witness_state input)
  |>.buffers.get! ⟨"output"⟩
  |>.last!

lemma constraints_closed_form {input : Felt} {output: BufferAtTime} :
  constraints input output ↔ (
    input = 0 ∧ output = [1,0,0].map some ∨
    input = 1 ∧ output = [0,1,0].map some ∨
    input = 2 ∧ output = [0,0,1].map some
  ) := by
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
