import Risc0.Map
import Risc0.MlirTactics
import Risc0.Optimisation
import Risc0.Gadgets.IsZero.Constraints.Code

namespace Risc0.IsZero.Constraints.Code

open MLIRNotation

def opt1 : MLIRProgram :=
  "%1" ←ₐ ⊤; "%2" ←ₐ .Get ⟨"in"⟩ 0 0; "%3" ←ₐ .Get ⟨"data"⟩ 0 0; "%4" ←ₐ ⟨"%1"⟩ &₀ ⟨"%2"⟩; "%5" ←ₐ guard ⟨"%3"⟩ & ⟨"%1"⟩ with ⟨"%4"⟩; "%0" ←ₐ .Const 1; "%6" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%7" ←ₐ .Get ⟨"data"⟩ 0 1; "%8" ←ₐ .Mul ⟨"%2"⟩ ⟨"%7"⟩; "%9" ←ₐ .Sub ⟨"%8"⟩ ⟨"%0"⟩; "%10" ←ₐ ⟨"%1"⟩ &₀ ⟨"%9"⟩; "%11" ←ₐ guard ⟨"%6"⟩ & ⟨"%5"⟩ with ⟨"%10"⟩
lemma optimised_behaviour1 :
  getReturn (full.runProgram st)  =
  getReturn (opt1.runProgram st)  := by
    unfold getReturn MLIR.runProgram full
    rewrite[opt_swap (const_past_true (by trivial)),opt_swap (const_past_get (by trivial)),opt_swap (const_past_get (by trivial)),opt_swap (const_past_andEqz (by trivial)),opt_swap (const_past_andCond (by trivial))]
    simp only [←MLIR.run_nondet]
    rewrite [←MLIR.run_seq_def]
    rewrite[←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def]

    unfold opt1
    with_reducible rfl

def opt2 : MLIRProgram :=
  "%1" ←ₐ ⊤; "%3" ←ₐ .Get ⟨"data"⟩ 0 0; "%2" ←ₐ .Get ⟨"in"⟩ 0 0; "%4" ←ₐ ⟨"%1"⟩ &₀ ⟨"%2"⟩; "%5" ←ₐ guard ⟨"%3"⟩ & ⟨"%1"⟩ with ⟨"%4"⟩; "%0" ←ₐ .Const 1; "%6" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%7" ←ₐ .Get ⟨"data"⟩ 0 1; "%8" ←ₐ .Mul ⟨"%2"⟩ ⟨"%7"⟩; "%9" ←ₐ .Sub ⟨"%8"⟩ ⟨"%0"⟩; "%10" ←ₐ ⟨"%1"⟩ &₀ ⟨"%9"⟩; "%11" ←ₐ guard ⟨"%6"⟩ & ⟨"%5"⟩ with ⟨"%10"⟩
lemma optimised_behaviour2 :
  getReturn (full.runProgram st)  =
  getReturn (opt2.runProgram st)  := by
    rewrite [optimised_behaviour1]
    unfold getReturn MLIR.runProgram opt1
    rewrite[MLIR.run_seq_def]
    rewrite[opt_swap (get_past_get_buf (by trivial) (by trivial))]
    simp only [←MLIR.run_nondet]
    rewrite [←MLIR.run_seq_def]
    rewrite[←MLIR.run_seq_def]

    unfold opt2
    with_reducible rfl

def opt3 : MLIRProgram :=
  "%1" ←ₐ ⊤; "%2" ←ₐ .Get ⟨"in"⟩ 0 0; "%4" ←ₐ ⟨"%1"⟩ &₀ ⟨"%2"⟩; "%3" ←ₐ .Get ⟨"data"⟩ 0 0; "%5" ←ₐ guard ⟨"%3"⟩ & ⟨"%1"⟩ with ⟨"%4"⟩; "%0" ←ₐ .Const 1; "%6" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%7" ←ₐ .Get ⟨"data"⟩ 0 1; "%8" ←ₐ .Mul ⟨"%2"⟩ ⟨"%7"⟩; "%9" ←ₐ .Sub ⟨"%8"⟩ ⟨"%0"⟩; "%10" ←ₐ ⟨"%1"⟩ &₀ ⟨"%9"⟩; "%11" ←ₐ guard ⟨"%6"⟩ & ⟨"%5"⟩ with ⟨"%10"⟩
lemma optimised_behaviour3 :
  getReturn (full.runProgram st)  =
  getReturn (opt3.runProgram st)  := by
    rewrite [optimised_behaviour2]
    unfold getReturn MLIR.runProgram opt2
    rewrite[MLIR.run_seq_def]
    rewrite[opt_swap (get_past_get_buf (by trivial) (by trivial)),opt_swap (get_past_andEqz (by trivial) (by trivial) (by trivial))]
    simp only [←MLIR.run_nondet]
    rewrite [←MLIR.run_seq_def]
    rewrite[←MLIR.run_seq_def,←MLIR.run_seq_def]

    unfold opt3
    with_reducible rfl

def opt_full : MLIRProgram := opt3
lemma opt_full_def : opt_full = opt3 := rfl
lemma optimised_behaviour_full :
  getReturn (full.runProgram st)  =
  getReturn (opt_full.runProgram st)  := by
  rewrite [optimised_behaviour3]
  rw [opt_full]
end Risc0.IsZero.Constraints.Code