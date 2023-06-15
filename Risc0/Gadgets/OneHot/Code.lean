-- import Mathlib.Data.Nat.Prime
-- import Mathlib.Data.Vector
-- import Mathlib.Data.ZMod.Defs
-- import Mathlib.Data.ZMod.Basic
-- import Mathlib.Tactic.FieldSimp

import Risc0.Basic
import Risc0.Lemmas
import Risc0.Wheels

namespace Risc0.OneHot.Code

open MLIRNotation

def constraints : MLIRProgram :=
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
  -- state'.props.get! ⟨"andEqz outputSum-1"⟩


namespace Witness

def full : MLIRProgram :=
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

def run (st: State) : BufferAtTime :=
  full.runProgram st |>.lastOutput

def part₀ : MLIRProgram :=
  -- %0 = cirgen.const 2
  "2" ←ₐ .Const 2;
  -- %1 = cirgen.const 1
  "1" ←ₐ .Const 1;
  -- %2 = cirgen.const 0
  "0" ←ₐ .Const 0;
  -- %3 = cirgen.get %arg0[0] back 0 : <1, constant>
  "input" ←ₐ .Get ⟨"input"⟩ 0 0

def part₁ : MLIRProgram :=
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

def part₂ : MLIRProgram :=
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

def part₃ : MLIRProgram :=
  -- %9 = cirgen.get %arg1[0] back 0 : <3, mutable>
  "output[0]" ←ₐ .Get ⟨"output"⟩ 0 0;
   -- %10 = cirgen.sub %1 : <default>, %9 : <default>
  "1 - Output[0]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[0]"⟩;
   -- %11 = cirgen.mul %9 : <default>, %10 : <default>
  "output[0] <= 1" ←ₐ .Mul ⟨"output[0]"⟩ ⟨"1 - Output[0]"⟩;
   -- cirgen.eqz %11 : <default>
  ?₀ ⟨"output[0] <= 1"⟩

def part₄ : MLIRProgram :=
  -- %12 = cirgen.sub %1 : <default>, %4 : <default>
  "1 - Output[1]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[1]"⟩;
   -- %13 = cirgen.mul %4 : <default>, %12 : <default>
  "output[1] <= 1" ←ₐ .Mul ⟨"output[1]"⟩ ⟨"1 - Output[1]"⟩;
   -- cirgen.eqz %13 : <default>
  ?₀ ⟨"output[1] <= 1"⟩

def part₅ : MLIRProgram :=
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

abbrev parts_combined : MLIRProgram :=
  part₀; part₁; part₂; part₃; part₄; part₅

lemma parts_combine {st: State} :
  Γ st ⟦full⟧ =
  Γ st ⟦parts_combined⟧ := by
  unfold full parts_combined
    part₀ part₁ part₂ part₃ part₄ part₅
  simp [MLIR.seq_assoc, MLIR.run_seq_def]

end Witness


-- namespace WitnessParts

-- namespace Setup0

-- def pre (st : State) (input : Felt) : Prop :=
--   st.Valid ∧
--   (st.buffers.get! ⟨"input"⟩ |>.last!) = [some input] ∧
--   (st.buffers.get! ⟨"output"⟩ |>.last!) = [none, none, none]

-- def prog : MLIRProgram :=
--   

-- def post (st: State) (input : Felt) : Prop :=
--   st.Valid ∧
--   st.hasFelts [("0", 0), ("1", 1), ("2", 2), ("input", input)] ∧
--   (st.buffers.get! ⟨"input"⟩ |>.last!) = [some input] ∧
--   (st.buffers.get! ⟨"output"⟩ |>.last!) = [none, none, none]
  
-- end Setup0

-- namespace Nondet1

-- def pre (st : State) (input : Felt) : Prop :=
--   st.felts.get! ⟨"input"⟩ = input ∧
--   st.felts.get! ⟨"1"⟩ = 1 ∧
--   st.felts.get! ⟨"2"⟩ = 2

-- def prog : MLIRProgram :=


-- lemma closed_form {input : Felt} (st: State) :
--   pre st input → (
--     (input = 0 → (prog.run st |>.buffers.get! ⟨"output"⟩ |>.last!) = [1,0,0].map some) ∧
--     (input = 1 → (prog.run st |>.buffers.get! ⟨"output"⟩ |>.last!) = [0,1,0].map some) ∧
--     (input = 2 → (prog.run st |>.buffers.get! ⟨"output"⟩ |>.last!) = [0,0,1].map some)
--   ) := by
--   sorry

-- end Nondet1

-- namespace Projection2

-- def pre (st : State) (input : Felt): Prop :=
--   st.WellFormed ∧
--   st.bufferWidths.get! ⟨"output"⟩ = 3 ∧
--   st.felts.get! ⟨"2"⟩ = 2 ∧
--   st.felts.get! ⟨"input"⟩ = input

-- def prog : MLIRProgram :=
--    -- %4 = cirgen.get %arg1[1] back 0 : <3, mutable>
--   "output[1]" ←ₐ .Get ⟨"output"⟩ 0 1;
--    -- %5 = cirgen.get %arg1[2] back 0 : <3, mutable>
--   "output[2]" ←ₐ .Get ⟨"output"⟩ 0 2;
--    -- %6 = cirgen.mul %5 : <default>, %0 : <default>
--   "output[2] * 2" ←ₐ .Mul ⟨"output[2]"⟩ ⟨"2"⟩;
--    -- %7 = cirgen.add %4 : <default>, %6 : <default>
--   "2*output[2]+output[1]" ←ₐ .Add ⟨"output[1]"⟩ ⟨"output[2] * 2"⟩;
--    -- %8 = cirgen.sub %7 : <default>, %3 : <default>
--   "2*output[2]+output[1] - input" ←ₐ .Sub ⟨"2*output[2]+output[1]"⟩ ⟨"input"⟩;
--    -- cirgen.eqz %8 : <default>
--   ?₀ ⟨"2*output[2]+output[1] - input"⟩

-- lemma closed_form {input : Felt} (st: State) :
--   pre st input → (
--     (prog.run st |>.buffers.get! ⟨"output"⟩ |>.get! (st.cycle, 1)).get! +
--     (prog.run st |>.buffers.get! ⟨"output"⟩ |>.get! (st.cycle, 2)).get! * 2 =
--     input
--   ) := by
--   sorry

-- end Projection2

-- namespace Output0Boolean3

-- def pre (st : State) : Prop :=
--   st.felts.get! ⟨"1"⟩ = 1 ∧
--   st.bufferWidths.get! ⟨"output"⟩ = 3

-- def prog : MLIRProgram :=
--   -- %9 = cirgen.get %arg1[0] back 0 : <3, mutable>
--   "output[0]" ←ₐ .Get ⟨"output"⟩ 0 0;
--    -- %10 = cirgen.sub %1 : <default>, %9 : <default>
--   "1 - Output[0]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[0]"⟩;
--    -- %11 = cirgen.mul %9 : <default>, %10 : <default>
--   "output[0] <= 1" ←ₐ .Mul ⟨"output[0]"⟩ ⟨"1 - Output[0]"⟩;
--    -- cirgen.eqz %11 : <default>
--   ?₀ ⟨"output[0] <= 1"⟩

-- def closed_form (st: State) :
--   pre st → (
--     (prog.run st |>.buffers.get! ⟨"output"⟩ |>.get! (st.cycle, 0)).get! = 0 ∨
--     (prog.run st |>.buffers.get! ⟨"output"⟩ |>.get! (st.cycle, 0)).get! = 1 -- Review: how to rewrite as ≤ 1? (getting failed to synthesize instance)
--   ) := by
--   sorry

-- end Output0Boolean3

-- namespace Output1Boolean4

-- def pre (st : State) : Prop :=
--   st.felts.get! ⟨"1"⟩ = 1 ∧
--   st.bufferWidths.get! ⟨"output"⟩ = 3

-- def prog : MLIRProgram :=
--   -- %12 = cirgen.sub %1 : <default>, %4 : <default>
--   "1 - Output[1]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[1]"⟩;
--    -- %13 = cirgen.mul %4 : <default>, %12 : <default>
--   "output[1] <= 1" ←ₐ .Mul ⟨"output[1]"⟩ ⟨"1 - Output[1]"⟩;
--    -- cirgen.eqz %13 : <default>
--   ?₀ ⟨"output[1] <= 1"⟩

-- def closed_form (st: State) :
--   pre st → (
--     (prog.run st |>.buffers.get! ⟨"output"⟩ |>.get! (st.cycle, 1)).get! = 0 ∨
--     (prog.run st |>.buffers.get! ⟨"output"⟩ |>.get! (st.cycle, 1)).get! = 1
--   ) := by
--   sorry

-- end Output1Boolean4

-- namespace FinalConstraints5

-- def pre (st: State) : Prop :=
--   st.felts.get! ⟨"1"⟩ = 1 ∧
--   st.felts.get! ⟨"output[0]"⟩ = (st.buffers.get! ⟨"output"⟩ |>.get! (st.cycle, 0)) ∧
--   st.felts.get! ⟨"output[0]"⟩ = (st.buffers.get! ⟨"output[1]"⟩ |>.get! (st.cycle, 1)) ∧
--   st.felts.get! ⟨"output[0]"⟩ = (st.buffers.get! ⟨"output[2]"⟩ |>.get! (st.cycle, 2))

-- def prog: MLIRProgram :=
--    -- %14 = cirgen.add %9 : <default>, %4 : <default>
--   "output[0]AddOutput[1]" ←ₐ .Add ⟨"output[0]"⟩ ⟨"output[1]"⟩;
--    -- %15 = cirgen.sub %1 : <default>, %5 : <default>
--   "1 - Output[2]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[2]"⟩;
--    -- %16 = cirgen.mul %5 : <default>, %15 : <default>
--   "output[2] <= 1" ←ₐ .Mul ⟨"output[2]"⟩ ⟨"1 - Output[2]"⟩;
--    -- cirgen.eqz %16 : <default>
--   ?₀ ⟨"output[2] <= 1"⟩;
--    -- %17 = cirgen.add %14 : <default>, %5 : <default>
--   "outputSum" ←ₐ .Add ⟨"output[0]AddOutput[1]"⟩ ⟨"output[2]"⟩;
--    -- %18 = cirgen.sub %17 : <default>, %1 : <default>
--   "outputSum - 1" ←ₐ .Sub ⟨"outputSum"⟩ ⟨"1"⟩;
--   --     cirgen.eqz %18 : <default>
--   ?₀ ⟨"outputSum - 1"⟩

-- def closed_form (st: State) :
--   pre st → (
--     (
--       (prog.run st |>.buffers.get! ⟨"output"⟩ |>.get! (st.cycle, 2)).get! = 0 ∨
--       (prog.run st |>.buffers.get! ⟨"output"⟩ |>.get! (st.cycle, 2)).get! = 1
--     ) ∧
--     (prog.run st |>.buffers.get! ⟨"output"⟩ |>.get! (st.cycle, 0)).get! +
--     (prog.run st |>.buffers.get! ⟨"output"⟩ |>.get! (st.cycle, 1)).get! +
--     (prog.run st |>.buffers.get! ⟨"output"⟩ |>.get! (st.cycle, 2)).get! = 1
--   ) := by
--   sorry

-- end FinalConstraints5

-- end WitnessParts

-- def witness (input : Felt) : BufferAtTime :=
--   witness_prog_full.run (initial_witness_state input)
--   |>.buffers.get! ⟨"output"⟩
--   |>.last!

-- lemma constraints_closed_form {input : Felt} {output: BufferAtTime} :
--   constraints input output ↔ (
--     input = 0 ∧ output = [1,0,0].map some ∨
--     input = 1 ∧ output = [0,1,0].map some ∨
--     input = 2 ∧ output = [0,0,1].map some
--   ) := by
--   sorry

-- lemma witness_closed_form {input : Felt} {output : BufferAtTime} :
--   witness input = output ↔ (
--     input = 0 ∧ output = [1,0,0].map some ∨
--     input = 1 ∧ output = [0,1,0].map some ∨
--     input = 2 ∧ output = [0,0,1].map some
--   ) := by
--   sorry

-- theorem witness_implies_constraints {input : Felt} {output : BufferAtTime} :
--   witness input = output → constraints input output := by
--   simp [constraints_closed_form, witness_closed_form]

-- end Risc0.OneHot


-- notes
-- start with _ as weakest pre
-- split the program into subprograms
-- prove evaluating concatenation of subprograms is same as full using seq assoc
-- initially do _ weakest pre for everything but generalize all but first
-- use MLIR and copy the state changes

-- from then run from the next part and repeat
-- create state_update def
-- weakest pre branch