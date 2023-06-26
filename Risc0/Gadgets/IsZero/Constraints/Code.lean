import Risc0.Basic
import Risc0.Lemmas

namespace Risc0.IsZero.Constraints.Code

open MLIRNotation

def full : MLIRProgram :=
  let one := 0
  let zero := 1
  let true_ := 2
  let x := 3
  let out0 := 4
  let andEqzX := 5
  let ifOut0ThenEqzX := 6
  let oneMinusOut0 := 7
  let out1 := 8
  let xTimesOut1 := 9
  let xTimesOut1Minus1 := 10
  let otherCond := 11
  let ifOtherCond := 12
  one         ←ₐ C 1; 
  zero         ←ₐ C 0;
  -- %1 = cirgen.true
  true_      ←ₐ ⊤;  
  -- %2 = cirgen.get %arg0[0] back 0 : <1, constant>
  x         ←ₐ .Get ⟨Input⟩ 0 0;
  -- %3 = cirgen.get %arg1[0] back 0 : <2, mutable>
  out0    ←ₐ .Get ⟨Output⟩ 0 0;
  -- %4 = cirgen.and_eqz %1, %2 : <default>
  andEqzX  ←ₐ ⟨true_⟩ &₀ ⟨x⟩;
  -- %5 = cirgen.and_cond %1, %3 : <default>, %4
  ifOut0ThenEqzX ←ₐ guard ⟨out0⟩ & ⟨true_⟩ with ⟨andEqzX⟩;
  -- %6 = cirgen.sub %0 : <default>, %3 : <default>
  oneMinusOut0 ←ₐ Op.Sub ⟨one⟩ ⟨out0⟩;
  -- %7 = cirgen.get %arg1[1] back 0 : <2, mutable>
  out1         ←ₐ .Get ⟨Output⟩ 0 1;
  -- %8 = cirgen.mul %2 : <default>, %7 : <default>
  xTimesOut1     ←ₐ Op.Mul ⟨x⟩ ⟨out1⟩; 
  -- %9 = cirgen.sub %8 : <default>, %0 : <default>
  xTimesOut1Minus1 ←ₐ Op.Sub ⟨xTimesOut1⟩ ⟨one⟩;
  -- %10 = cirgen.and_eqz %1, %9 : <default>
  otherCond ←ₐ ⟨true_⟩ &₀ ⟨xTimesOut1Minus1⟩; 
  -- %11 = cirgen.and_cond %5, %6 : <default>, %10
  ifOtherCond ←ₐ guard ⟨oneMinusOut0⟩ & ⟨ifOut0ThenEqzX⟩ with ⟨otherCond⟩

def getReturn (st: State) : Prop :=
  let ifOtherCond := 12 
  st.constraintsInVar ⟨ifOtherCond⟩

def run (st: State) : Prop :=
  getReturn (full.runProgram st)

def part₀ : MLIRProgram :=
  let one := 0
  let zero := 1
  let true_ := 2
  one         ←ₐ C 1; 
  zero         ←ₐ C 0;
  -- %1 = cirgen.true
  true_      ←ₐ ⊤

def part₁ : MLIRProgram :=
  let true_ := 2
  let x := 3
  let out0 := 4
  let andEqzX := 5
  -- %2 = cirgen.get %arg0[0] back 0 : <1, constant>
  x         ←ₐ .Get ⟨Input⟩ 0 0;
  -- %3 = cirgen.get %arg1[0] back 0 : <2, mutable>
  out0    ←ₐ .Get ⟨Output⟩ 0 0;
  -- %4 = cirgen.and_eqz %1, %2 : <default>
  andEqzX  ←ₐ ⟨true_⟩ &₀ ⟨x⟩

def part₂ : MLIRProgram :=
  let one := 0
  let true_ := 2
  let out0 := 4
  let andEqzX := 5
  let ifOut0ThenEqzX := 6
  let oneMinusOut0 := 7
  let out1 := 8
  ifOut0ThenEqzX ←ₐ guard ⟨out0⟩ & ⟨true_⟩ with ⟨andEqzX⟩;
  -- %6 = cirgen.sub %0 : <default>, %3 : <default>
  oneMinusOut0 ←ₐ Op.Sub ⟨one⟩ ⟨out0⟩;
  -- %7 = cirgen.get %arg1[1] back 0 : <2, mutable>
  out1         ←ₐ .Get ⟨Output⟩ 0 1

def part₃ : MLIRProgram :=
  let one := 0
  let true_ := 2
  let x := 3
  let out1 := 8
  let xTimesOut1 := 9
  let xTimesOut1Minus1 := 10
  let otherCond := 11
  -- %8 = cirgen.mul %2 : <default>, %7 : <default>
  xTimesOut1     ←ₐ Op.Mul ⟨x⟩ ⟨out1⟩; 
  -- %9 = cirgen.sub %8 : <default>, %0 : <default>
  xTimesOut1Minus1 ←ₐ Op.Sub ⟨xTimesOut1⟩ ⟨one⟩;
  -- %10 = cirgen.and_eqz %1, %9 : <default>
  otherCond ←ₐ ⟨true_⟩ &₀ ⟨xTimesOut1Minus1⟩

def part₄ : MLIRProgram :=
  let ifOut0ThenEqzX := 6
  let oneMinusOut0 := 7
  let otherCond := 11
  let ifOtherCond := 12
  -- %11 = cirgen.and_cond %5, %6 : <default>, %10
  ifOtherCond ←ₐ guard ⟨oneMinusOut0⟩ & ⟨ifOut0ThenEqzX⟩ with ⟨otherCond⟩

abbrev parts_combined : MLIRProgram :=
  part₀; part₁; part₂; part₃; part₄

lemma parts_combine {st: State} :
  Γ st ⟦full⟧ =
  Γ st ⟦parts_combined⟧ := by
  unfold full parts_combined
    part₀ part₁ part₂ part₃ part₄
  simp [MLIR.seq_assoc, MLIR.run_seq_def]

end Risc0.IsZero.Constraints.Code
