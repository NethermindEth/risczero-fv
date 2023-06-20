import Risc0.Basic
import Risc0.Lemmas

namespace Risc0.IsZero.Witness.Code

open MLIRNotation

def full : MLIRProgram :=
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

def run (st: State) : BufferAtTime :=
  full.runProgram st |>.lastOutput

def part₀ : MLIRProgram :=
  "1" ←ₐ .Const 1;
  "x" ←ₐ Op.Get ⟨"input"⟩ 0 0

def part₁ : MLIRProgram := nondet (
    "isZeroBit" ←ₐ ??₀⟨"x"⟩;
    ⟨"output"⟩[0]   ←ᵢ ⟨"isZeroBit"⟩;
    "invVal"    ←ₐ Inv ⟨"x"⟩;
    ⟨"output"⟩[1]   ←ᵢ ⟨"invVal"⟩  
  )

def part₂ : MLIRProgram := "arg1[0]" ←ₐ .Get ⟨"output"⟩ 0 0

def part₃ : MLIRProgram := guard ⟨"arg1[0]"⟩ then ?₀ ⟨"x"⟩

def part₄ : MLIRProgram := "1 - arg1[0]" ←ₐ .Sub ⟨"1"⟩ ⟨"arg1[0]"⟩

def part₅ : MLIRProgram :=
  guard ⟨"1 - arg1[0]"⟩ then
    "arg1[1]"        ←ₐ .Get ⟨"output"⟩ 0 1;
    "x * arg1[1]"     ←ₐ .Mul ⟨"x"⟩ ⟨"arg1[1]"⟩;
    "x * arg1[1] - 1" ←ₐ .Sub ⟨"x * arg1[1]"⟩ ⟨"1"⟩;
    ?₀ ⟨"x * arg1[1] - 1"⟩

abbrev parts_combined : MLIRProgram :=
  part₀; part₁; part₂; part₃; part₄; part₅

lemma parts_combine {st: State} :
  Γ st ⟦full⟧ =
  Γ st ⟦parts_combined⟧ := by
  unfold full parts_combined
    part₀ part₁ part₂ part₃ part₄ part₅
  simp [MLIR.seq_assoc, MLIR.run_seq_def, MLIR.nondet_blocks_split]

end Risc0.IsZero.Witness.Code
