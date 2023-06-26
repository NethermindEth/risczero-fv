import Risc0.Basic
import Risc0.Lemmas

namespace Risc0.IsZero.Witness.Code

open MLIRNotation

def full : MLIRProgram :=
  let one := 0
  let x := 1
  let isZeroBit := 2
  let invVal := 3
  let arg10 := 4
  let oneMinusArg10 := 5
  let arg11 := 6
  let xTimesArg11 := 7
  let xTimesArg11Minus1 := 8
  one         ←ₐ .Const 1;
  x         ←ₐ Op.Get ⟨Input⟩ 0 0;
  nondet (
    isZeroBit ←ₐ ??₀⟨x⟩;
    ⟨Output⟩[0]   ←ᵢ ⟨isZeroBit⟩;
    invVal    ←ₐ Inv ⟨x⟩;
    ⟨Output⟩[1]   ←ᵢ ⟨invVal⟩  
  );
  arg10   ←ₐ .Get ⟨Output⟩ 0 0;
  guard ⟨arg10⟩ then
    ?₀ ⟨x⟩;
  oneMinusArg10 ←ₐ .Sub ⟨one⟩ ⟨arg10⟩;
  guard ⟨oneMinusArg10⟩ then
    arg11        ←ₐ .Get ⟨Output⟩ 0 1;
    xTimesArg11     ←ₐ .Mul ⟨x⟩ ⟨arg11⟩;
    xTimesArg11Minus1 ←ₐ .Sub ⟨xTimesArg11⟩ ⟨one⟩;
    ?₀ ⟨xTimesArg11Minus1⟩

def run (st: State) : BufferAtTime :=
  full.runProgram st |>.lastOutput

def part₀ : MLIRProgram :=
  let one := 0
  let x := 1
  one         ←ₐ .Const 1;
  x         ←ₐ Op.Get ⟨Input⟩ 0 0

def part₁ : MLIRProgram := 
  let x := 1
  let isZeroBit := 2
  let invVal := 3
  nondet (
    isZeroBit ←ₐ ??₀⟨x⟩;
    ⟨Output⟩[0]   ←ᵢ ⟨isZeroBit⟩;
    invVal    ←ₐ Inv ⟨x⟩;
    ⟨Output⟩[1]   ←ᵢ ⟨invVal⟩  
  )

def part₂ : MLIRProgram := 
  let arg10 := 4
  arg10   ←ₐ .Get ⟨Output⟩ 0 0

def part₃ : MLIRProgram := 
  let x := 1
  let arg10 := 4
  guard ⟨arg10⟩ then ?₀ ⟨x⟩

def part₄ : MLIRProgram := 
  let one := 0
  let arg10 := 4
  let oneMinusArg10 := 5
  oneMinusArg10 ←ₐ .Sub ⟨one⟩ ⟨arg10⟩

def part₅ : MLIRProgram :=
  let one := 0
  let x := 1
  let oneMinusArg10 := 5
  let arg11 := 6
  let xTimesArg11 := 7
  let xTimesArg11Minus1 := 8
  guard ⟨oneMinusArg10⟩ then
    arg11        ←ₐ .Get ⟨Output⟩ 0 1;
    xTimesArg11     ←ₐ .Mul ⟨x⟩ ⟨arg11⟩;
    xTimesArg11Minus1 ←ₐ .Sub ⟨xTimesArg11⟩ ⟨one⟩;
    ?₀ ⟨xTimesArg11Minus1⟩

abbrev parts_combined : MLIRProgram :=
  part₀; part₁; part₂; part₃; part₄; part₅

lemma parts_combine {st: State} :
  Γ st ⟦full⟧ =
  Γ st ⟦parts_combined⟧ := by
  unfold full parts_combined
    part₀ part₁ part₂ part₃ part₄ part₅
  simp [MLIR.seq_assoc, MLIR.run_seq_def, MLIR.nondet_blocks_split]

end Risc0.IsZero.Witness.Code
