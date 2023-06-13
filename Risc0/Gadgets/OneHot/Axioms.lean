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

namespace WitnessParts

namespace Setup0

def prog : MLIRProgram :=
-- %0 = cirgen.const 2
  "2" ←ₐ .Const 2;
  -- %1 = cirgen.const 1
  "1" ←ₐ .Const 1;
  -- %2 = cirgen.const 0
  "0" ←ₐ .Const 0;
  -- %3 = cirgen.get %arg0[0] back 0 : <1, constant>
  "input" ←ₐ .Get ⟨"input"⟩ 0 0

lemma closed_form {input : Felt} :
  (prog.run (initial_witness_state input)).felts.get! ⟨"2"⟩ = 2 ∧
  (prog.run (initial_witness_state input)).felts.get! ⟨"1"⟩ = 1 ∧
  (prog.run (initial_witness_state input)).felts.get! ⟨"0"⟩ = 0 ∧
  (prog.run (initial_witness_state input)).felts.get! ⟨"input"⟩ = input := by
  aesop
  
end Setup0

namespace Nondet1

def pre (st : State) (input : Felt) : Prop :=
  st.felts.get! ⟨"input"⟩ = input ∧
  st.felts.get! ⟨"1"⟩ = 1 ∧
  st.felts.get! ⟨"2"⟩ = 2

def prog : MLIRProgram :=
   -- cirgen.nondet {
  nondet (
     --   %19 = cirgen.isz %3 : <default>
    "input == 0" ←ₐ ??₀⟨"input"⟩;
     --   cirgen.set %arg1 : <3, mutable>[0] = %19 : <default>
    ⟨"output"⟩[0] ←ᵢ ⟨"input == 0"⟩;
     --   %20 = cirgen.sub %3 : <default>, %1 : <default>
    "input - 1" ←ₐ .Sub ⟨"input"⟩ ⟨"1"⟩;
     --   %21 = cirgen.isz %20 : <default>
    "input == 1" ←ₐ ??₀⟨"input - 1"⟩;
     --   cirgen.set %arg1 : <3, mutable>[1] = %21 : <default>
    ⟨"output"⟩[1] ←ᵢ ⟨"input == 1"⟩;
     --   %22 = cirgen.sub %3 : <default>, %0 : <default>
    "input - 2" ←ₐ .Sub ⟨"input"⟩ ⟨"2"⟩;
     --   %23 = cirgen.isz %22 : <default>
    "input == 2" ←ₐ ??₀⟨"input - 2"⟩;
     --   cirgen.set %arg1 : <3, mutable>[2] = %23 : <default>
    ⟨"output"⟩[2] ←ᵢ ⟨"input == 2"⟩
     -- }
  )

lemma closed_form {input : Felt} (st: State) :
  pre st input → (
    (input = 0 → (prog.run st |>.buffers.get! ⟨"output"⟩ |>.last!) = [1,0,0].map some) ∧
    (input = 1 → (prog.run st |>.buffers.get! ⟨"output"⟩ |>.last!) = [0,1,0].map some) ∧
    (input = 2 → (prog.run st |>.buffers.get! ⟨"output"⟩ |>.last!) = [0,0,1].map some)
  ) := by
  sorry

end Nondet1

end WitnessParts



def witness_prog_2_projection : MLIRProgram :=
   -- %4 = cirgen.get %arg1[1] back 0 : <3, mutable>
  "output[1]" ←ₐ .Get ⟨"output"⟩ 0 1;
   -- %5 = cirgen.get %arg1[2] back 0 : <3, mutable>
  "output[2]" ←ₐ .Get ⟨"output"⟩ 0 2;
   -- %6 = cirgen.mul %5 : <default>, %0 : <default>
  "output[2] * 2" ←ₐ .Mul ⟨"output[2]"⟩ ⟨"2"⟩;
   -- %7 = cirgen.add %4 : <default>, %6 : <default>
  "2*output[2]+output[1]" ←ₐ .Add ⟨"output[1]"⟩ ⟨"output[2] * 2"⟩;
   -- %8 = cirgen.sub %7 : <default>, %3 : <default>
  "2*output[2]+output[1] - input" ←ₐ .Sub ⟨"2*output[2]+output[1]"⟩ ⟨"input"⟩;
   -- cirgen.eqz %8 : <default>
  ?₀ ⟨"2*output[2]+output[1] - input"⟩

def witness_prog_3_output0_le_1 : MLIRProgram :=
   -- %9 = cirgen.get %arg1[0] back 0 : <3, mutable>
  "output[0]" ←ₐ .Get ⟨"output"⟩ 0 0;
   -- %10 = cirgen.sub %1 : <default>, %9 : <default>
  "1 - Output[0]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[0]"⟩;
   -- %11 = cirgen.mul %9 : <default>, %10 : <default>
  "output[0] <= 1" ←ₐ .Mul ⟨"output[0]"⟩ ⟨"1 - Output[0]"⟩;
   -- cirgen.eqz %11 : <default>
  ?₀ ⟨"output[0] <= 1"⟩

def witness_prog_3_output1_le_1 : MLIRProgram :=
   -- %12 = cirgen.sub %1 : <default>, %4 : <default>
  "1 - Output[1]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[1]"⟩;
   -- %13 = cirgen.mul %4 : <default>, %12 : <default>
  "output[1] <= 1" ←ₐ .Mul ⟨"output[1]"⟩ ⟨"1 - Output[1]"⟩;
   -- cirgen.eqz %13 : <default>
  ?₀ ⟨"output[1] <= 1"⟩

def witness_prog_4_final_constraints : MLIRProgram :=
   -- %14 = cirgen.add %9 : <default>, %4 : <default>
  "output[0]AddOutput[1]" ←ₐ .Add ⟨"output[0]"⟩ ⟨"output[1]"⟩;
   -- %15 = cirgen.sub %1 : <default>, %5 : <default>
  "1 - Output[2]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[2]"⟩;
   -- %16 = cirgen.mul %5 : <default>, %15 : <default>
  "output[2] <= 1" ←ₐ .Mul ⟨"output[2]"⟩ ⟨"1 - Output[2]"⟩;
   -- cirgen.eqz %16 : <default>
  ?₀ ⟨"output[2] <= 1"⟩;
   -- %17 = cirgen.add %14 : <default>, %5 : <default>
  "outputSum" ←ₐ .Add ⟨"output[0]AddOutput[1]"⟩ ⟨"output[2]"⟩;
   -- %18 = cirgen.sub %17 : <default>, %1 : <default>
  "outputSum - 1" ←ₐ .Sub ⟨"outputSum"⟩ ⟨"1"⟩;
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
