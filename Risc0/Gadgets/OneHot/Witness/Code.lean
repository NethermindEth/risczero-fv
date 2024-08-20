import Risc0.Cirgen
import Risc0.Lemmas
import Risc0.Wheels

namespace Risc0.OneHot.Witness.Code

open MLIRNotation

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
    "input == 1" ←ₐ ??₀⟨"input - 1"⟩
     -- }
  )

def part₂ : MLIRProgram :=
   -- cirgen.nondet {
  nondet (
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

def part₃ : MLIRProgram :=
   -- %4 = cirgen.get %arg1[1] back 0 : <3, mutable>
  "output[1]" ←ₐ .Get ⟨"output"⟩ 0 1;
   -- %5 = cirgen.get %arg1[2] back 0 : <3, mutable>
  "output[2]" ←ₐ .Get ⟨"output"⟩ 0 2

def part₄ : MLIRProgram :=
   -- %6 = cirgen.mul %5 : <default>, %0 : <default>
  "output[2] * 2" ←ₐ .Mul ⟨"output[2]"⟩ ⟨"2"⟩;
   -- %7 = cirgen.add %4 : <default>, %6 : <default>
  "2*output[2]+output[1]" ←ₐ .Add ⟨"output[1]"⟩ ⟨"output[2] * 2"⟩;
   -- %8 = cirgen.sub %7 : <default>, %3 : <default>
  "2*output[2]+output[1] - input" ←ₐ .Sub ⟨"2*output[2]+output[1]"⟩ ⟨"input"⟩;
   -- cirgen.eqz %8 : <default>
  ?₀ ⟨"2*output[2]+output[1] - input"⟩

def part₅ : MLIRProgram :=
  -- %9 = cirgen.get %arg1[0] back 0 : <3, mutable>
  "output[0]" ←ₐ .Get ⟨"output"⟩ 0 0;
   -- %10 = cirgen.sub %1 : <default>, %9 : <default>
  "1 - Output[0]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[0]"⟩;
   -- %11 = cirgen.mul %9 : <default>, %10 : <default>
  "output[0] <= 1" ←ₐ .Mul ⟨"output[0]"⟩ ⟨"1 - Output[0]"⟩;
   -- cirgen.eqz %11 : <default>
  ?₀ ⟨"output[0] <= 1"⟩

def part₆ : MLIRProgram :=
  -- %12 = cirgen.sub %1 : <default>, %4 : <default>
  "1 - Output[1]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[1]"⟩;
   -- %13 = cirgen.mul %4 : <default>, %12 : <default>
  "output[1] <= 1" ←ₐ .Mul ⟨"output[1]"⟩ ⟨"1 - Output[1]"⟩;
   -- cirgen.eqz %13 : <default>
  ?₀ ⟨"output[1] <= 1"⟩

def part₇ : MLIRProgram :=
   -- %14 = cirgen.add %9 : <default>, %4 : <default>
  "output[0]AddOutput[1]" ←ₐ .Add ⟨"output[0]"⟩ ⟨"output[1]"⟩;
   -- %15 = cirgen.sub %1 : <default>, %5 : <default>
  "1 - Output[2]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[2]"⟩;
   -- %16 = cirgen.mul %5 : <default>, %15 : <default>
  "output[2] <= 1" ←ₐ .Mul ⟨"output[2]"⟩ ⟨"1 - Output[2]"⟩;
   -- cirgen.eqz %16 : <default>
  ?₀ ⟨"output[2] <= 1"⟩

def part₈ : MLIRProgram :=
   -- %17 = cirgen.add %14 : <default>, %5 : <default>
  "outputSum" ←ₐ .Add ⟨"output[0]AddOutput[1]"⟩ ⟨"output[2]"⟩;
   -- %18 = cirgen.sub %17 : <default>, %1 : <default>
  "outputSum - 1" ←ₐ .Sub ⟨"outputSum"⟩ ⟨"1"⟩;
  --     cirgen.eqz %18 : <default>
  ?₀ ⟨"outputSum - 1"⟩

abbrev parts_combined : MLIRProgram :=
  part₀; part₁; part₂; part₃; part₄; part₅; part₆; part₇; part₈

lemma parts_combine {st: State} :
  Γ st ⟦full⟧ =
  Γ st ⟦parts_combined⟧ := by
  unfold full parts_combined
    part₀ part₁ part₂ part₃ part₄ part₅ part₆ part₇ part₈
  simp [MLIR.seq_assoc, MLIR.run_seq_def, MLIR.nondet_blocks_split]

end Risc0.OneHot.Witness.Code
