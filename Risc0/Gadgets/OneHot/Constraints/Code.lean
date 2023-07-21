import Risc0.Cirgen
import Risc0.Lemmas
import Risc0.Wheels

namespace Risc0.OneHot.Constraints.Code

open MLIRNotation

def full : MLIRProgram :=
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

def getReturn (st: State) : Prop :=
  st.constraintsInVar ⟨"andEqz outputSum-1"⟩

def run (st: State) : Prop :=
  getReturn (full.runProgram st)

def part₀ : MLIRProgram :=
  --     %0 = cirgen.const 1  
  "1" ←ₐ C 1;
  --     %1 = cirgen.const 2
  "2" ←ₐ C 2;
  --     %2 = cirgen.true
  "true" ←ₐ ⊤;
  --     %3 = cirgen.get %arg0[0] back 0 : <1, constant>
  "input" ←ₐ .Get ⟨"input"⟩ 0 0

def part₁ : MLIRProgram :=
  --     %4 = cirgen.get %arg1[1] back 0 : <3, mutable>
  "output[1]" ←ₐ .Get ⟨"output"⟩ 0 1;
  --     %5 = cirgen.get %arg1[2] back 0 : <3, mutable>
  "output[2]" ←ₐ .Get ⟨"output"⟩ 0 2

def part₂ : MLIRProgram :=
  --     %6 = cirgen.mul %5 : <default>, %1 : <default>
  "output[2]*2" ←ₐ .Mul ⟨"output[2]"⟩ ⟨"2"⟩;
  --     %7 = cirgen.add %4 : <default>, %6 : <default>
  "2*output[2]+output[1]" ←ₐ .Add ⟨"output[1]"⟩ ⟨"output[2]*2"⟩

def part₃ : MLIRProgram :=
  --     %8 = cirgen.sub %7 : <default>, %3 : <default>
  "2*output[2]+output[1]-input" ←ₐ .Sub ⟨"2*output[2]+output[1]"⟩ ⟨"input"⟩;
  --     %9 = cirgen.and_eqz %2, %8 : <default>
  "andEqz 2*output[2]+output[1]-input" ←ₐ ⟨"true"⟩ &₀ ⟨"2*output[2]+output[1]-input"⟩;
  --     %10 = cirgen.get %arg1[0] back 0 : <3, mutable>
  "output[0]" ←ₐ .Get ⟨"output"⟩ 0 0;
  --     %11 = cirgen.sub %0 : <default>, %10 : <default>
  "1-Output[0]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[0]"⟩

def part₄ : MLIRProgram :=
  --     %12 = cirgen.mul %10 : <default>, %11 : <default>
  "output[0]<=1" ←ₐ .Mul ⟨"output[0]"⟩ ⟨"1-Output[0]"⟩;
  --     %13 = cirgen.and_eqz %9, %12 : <default>
  "andEqz output[0]<=1" ←ₐ ⟨"andEqz 2*output[2]+output[1]-input"⟩ &₀ ⟨"output[0]<=1"⟩;
  --     %14 = cirgen.sub %0 : <default>, %4 : <default>
  "1-Output[1]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[1]"⟩;
  --     %15 = cirgen.mul %4 : <default>, %14 : <default>
  "output[1]<=1" ←ₐ .Mul ⟨"output[1]"⟩ ⟨"1-Output[1]"⟩

def part₅ : MLIRProgram :=
  --     %16 = cirgen.and_eqz %13, %15 : <default>
  "andEqz output[1]<=1" ←ₐ ⟨"andEqz output[0]<=1"⟩ &₀ ⟨"output[1]<=1"⟩;
  --     %17 = cirgen.add %10 : <default>, %4 : <default>
  "output[0]+Output[1]" ←ₐ .Add ⟨"output[0]"⟩ ⟨"output[1]"⟩;
  --     %18 = cirgen.sub %0 : <default>, %5 : <default>
  "1-Output[2]" ←ₐ .Sub ⟨"1"⟩ ⟨"output[2]"⟩;
  --     %19 = cirgen.mul %5 : <default>, %18 : <default>
  "output[2]<=1" ←ₐ .Mul ⟨"output[1]"⟩ ⟨"1-Output[1]"⟩

def part₆ : MLIRProgram :=
  --     %20 = cirgen.and_eqz %16, %19 : <default>
  "andEqz output[2]<=1" ←ₐ ⟨"andEqz output[1]<=1"⟩ &₀ ⟨"output[2]<=1"⟩;
  --     %21 = cirgen.add %17 : <default>, %5 : <default>
  "outputSum" ←ₐ .Add ⟨"output[0]+Output[1]"⟩ ⟨"output[2]"⟩;
  --     %22 = cirgen.sub %21 : <default>, %0 : <default>
  "outputSum-1" ←ₐ .Sub ⟨"outputSum"⟩ ⟨"1"⟩;
  --     %23 = cirgen.and_eqz %20, %22 : <default>
  "andEqz outputSum-1" ←ₐ ⟨"andEqz output[2]<=1"⟩ &₀ ⟨"outputSum-1"⟩

abbrev parts_combined : MLIRProgram :=
  part₀; part₁; part₂; part₃; part₄; part₅; part₆

lemma parts_combine {st: State} :
  Γ st ⟦full⟧ =
  Γ st ⟦parts_combined⟧ := by
  unfold full parts_combined
    part₀ part₁ part₂ part₃ part₄ part₅ part₆
  simp [MLIR.seq_assoc, MLIR.run_seq_def]

end Risc0.OneHot.Constraints.Code
