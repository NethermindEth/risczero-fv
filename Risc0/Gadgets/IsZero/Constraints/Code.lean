import Risc0.Basic
import Risc0.Lemmas

namespace Risc0.IsZero.Constraints.Code

open MLIRNotation

def full : MLIRProgram :=
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

def getReturn (st: State) : Prop :=
  st.constraintsInVar ⟨"if other cond"⟩ ∧ ¬st.isFailed

def run (st: State) : Prop :=
  getReturn (full.runProgram st)

def part₀ : MLIRProgram :=
  "1"         ←ₐ C 1; 
  "0"         ←ₐ C 0;
  -- %1 = cirgen.true
  "true"      ←ₐ ⊤ 

def part₁ : MLIRProgram :=
  -- %2 = cirgen.get %arg0[0] back 0 : <1, constant>
  "x"         ←ₐ .Get ⟨"input"⟩ 0 0;
  -- %3 = cirgen.get %arg1[0] back 0 : <2, mutable>
  "out[0]"    ←ₐ .Get ⟨"output"⟩ 0 0;
  -- %4 = cirgen.and_eqz %1, %2 : <default>
  "andEqz x"  ←ₐ ⟨"true"⟩ &₀ ⟨"x"⟩

def part₂ : MLIRProgram :=
  -- %5 = cirgen.and_cond %1, %3 : <default>, %4
  "if out[0] then eqz x" ←ₐ guard ⟨"out[0]"⟩ & ⟨"true"⟩ with ⟨"andEqz x"⟩;  
  -- %6 = cirgen.sub %0 : <default>, %3 : <default>
  "1 - out[0]" ←ₐ Op.Sub ⟨"1"⟩ ⟨"out[0]"⟩;
  -- %7 = cirgen.get %arg1[1] back 0 : <2, mutable>
  "out[1]"         ←ₐ .Get ⟨"output"⟩ 0 1

def part₃ : MLIRProgram :=
  -- %8 = cirgen.mul %2 : <default>, %7 : <default>
  "x * out[1]"     ←ₐ Op.Mul ⟨"x"⟩ ⟨"out[1]"⟩; 
  -- %9 = cirgen.sub %8 : <default>, %0 : <default>
  "x * out[1] - 1" ←ₐ Op.Sub ⟨"x * out[1]"⟩ ⟨"1"⟩;
  -- %10 = cirgen.and_eqz %1, %9 : <default>
  "other cond" ←ₐ ⟨"true"⟩ &₀ ⟨"x * out[1] - 1"⟩

def part₄ : MLIRProgram :=
  -- %11 = cirgen.and_cond %5, %6 : <default>, %10
  "if other cond" ←ₐ guard ⟨"1 - out[0]"⟩ & ⟨"if out[0] then eqz x"⟩ with ⟨"other cond"⟩

abbrev parts_combined : MLIRProgram :=
  part₀; part₁; part₂; part₃; part₄

lemma parts_combine {st: State} :
  Γ st ⟦full⟧ =
  Γ st ⟦parts_combined⟧ := by
  unfold full parts_combined
    part₀ part₁ part₂ part₃ part₄
  simp [MLIR.seq_assoc, MLIR.run_seq_def]

end Risc0.IsZero.Constraints.Code
