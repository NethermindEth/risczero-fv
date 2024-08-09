import Risc0.Map
import Risc0.MlirTactics
import Risc0.Optimisation
import Risc0.Gadgets.OneHot1.Constraints.Code

namespace Risc0.OneHot1.Constraints.Code

open MLIRNotation

def opt1 : MLIRProgram :=
  "%1" ←ₐ .Const 1; "%2" ←ₐ ⊤; "%3" ←ₐ .Get ⟨"code"⟩ 0 0; "%0" ←ₐ .Const 0; "%4" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%5" ←ₐ ⟨"%2"⟩ &₀ ⟨"%4"⟩; "%6" ←ₐ .Get ⟨"data"⟩ 0 0; "%7" ←ₐ .Sub ⟨"%1"⟩ ⟨"%6"⟩; "%8" ←ₐ .Mul ⟨"%6"⟩ ⟨"%7"⟩; "%9" ←ₐ ⟨"%5"⟩ &₀ ⟨"%8"⟩; "%10" ←ₐ .Sub ⟨"%6"⟩ ⟨"%1"⟩; "%11" ←ₐ ⟨"%9"⟩ &₀ ⟨"%10"⟩
lemma optimised_behaviour1 :
  getReturn (full.runProgram st)  =
  getReturn (opt1.runProgram st)  := by
    unfold getReturn MLIR.runProgram full
    rewrite[opt_swap (const_past_const (by trivial)),opt_swap (const_past_true (by trivial)),opt_swap (const_past_get (by trivial))]
    try simp only [←MLIR.run_nondet]
    rewrite [←MLIR.run_seq_def]
    rewrite[←MLIR.run_seq_def,←MLIR.run_seq_def]
    unfold opt1
    simp only

def opt2 : MLIRProgram :=
  "%2" ←ₐ ⊤; "%3" ←ₐ .Get ⟨"code"⟩ 0 0; "%0" ←ₐ .Const 0; "%4" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%5" ←ₐ ⟨"%2"⟩ &₀ ⟨"%4"⟩; "%6" ←ₐ .Get ⟨"data"⟩ 0 0; "%1" ←ₐ .Const 1; "%7" ←ₐ .Sub ⟨"%1"⟩ ⟨"%6"⟩; "%8" ←ₐ .Mul ⟨"%6"⟩ ⟨"%7"⟩; "%9" ←ₐ ⟨"%5"⟩ &₀ ⟨"%8"⟩; "%10" ←ₐ .Sub ⟨"%6"⟩ ⟨"%1"⟩; "%11" ←ₐ ⟨"%9"⟩ &₀ ⟨"%10"⟩
lemma optimised_behaviour2 :
  getReturn (full.runProgram st)  =
  getReturn (opt2.runProgram st)  := by
    rewrite [optimised_behaviour1]
    unfold getReturn MLIR.runProgram opt1
    rewrite[opt_swap (const_past_true (by trivial)),opt_swap (const_past_get (by trivial)),opt_swap (const_past_const (by trivial)),opt_swap (const_past_sub (by trivial) (by trivial) (by trivial)),opt_swap (const_past_andEqz (by trivial)),opt_swap (const_past_get (by trivial))]
    try simp only [←MLIR.run_nondet]
    rewrite [←MLIR.run_seq_def]
    rewrite[←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def]
    unfold opt2
    simp only

def opt3 : MLIRProgram :=
  "%2" ←ₐ ⊤; "%0" ←ₐ .Const 0; "%3" ←ₐ .Get ⟨"code"⟩ 0 0; "%4" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%5" ←ₐ ⟨"%2"⟩ &₀ ⟨"%4"⟩; "%6" ←ₐ .Get ⟨"data"⟩ 0 0; "%1" ←ₐ .Const 1; "%7" ←ₐ .Sub ⟨"%1"⟩ ⟨"%6"⟩; "%8" ←ₐ .Mul ⟨"%6"⟩ ⟨"%7"⟩; "%9" ←ₐ ⟨"%5"⟩ &₀ ⟨"%8"⟩; "%10" ←ₐ .Sub ⟨"%6"⟩ ⟨"%1"⟩; "%11" ←ₐ ⟨"%9"⟩ &₀ ⟨"%10"⟩
lemma optimised_behaviour3 :
  getReturn (full.runProgram st)  =
  getReturn (opt3.runProgram st)  := by
    rewrite [optimised_behaviour2]
    unfold getReturn MLIR.runProgram opt2
    rewrite[MLIR.run_seq_def]
    rewrite[opt_swap (get_past_const (by trivial))]
    try simp only [←MLIR.run_nondet]
    rewrite [←MLIR.run_seq_def]
    rewrite[←MLIR.run_seq_def]
    unfold opt3
    simp only

def opt4 : MLIRProgram :=
  "%2" ←ₐ ⊤; "%0" ←ₐ .Const 0; "%3" ←ₐ .Get ⟨"code"⟩ 0 0; "%4" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%5" ←ₐ ⟨"%2"⟩ &₀ ⟨"%4"⟩; "%1" ←ₐ .Const 1; "%6" ←ₐ .Get ⟨"data"⟩ 0 0; "%7" ←ₐ .Sub ⟨"%1"⟩ ⟨"%6"⟩; "%8" ←ₐ .Mul ⟨"%6"⟩ ⟨"%7"⟩; "%9" ←ₐ ⟨"%5"⟩ &₀ ⟨"%8"⟩; "%10" ←ₐ .Sub ⟨"%6"⟩ ⟨"%1"⟩; "%11" ←ₐ ⟨"%9"⟩ &₀ ⟨"%10"⟩
lemma optimised_behaviour4 :
  getReturn (full.runProgram st)  =
  getReturn (opt4.runProgram st)  := by
    rewrite [optimised_behaviour3]
    unfold getReturn MLIR.runProgram opt3
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite[opt_swap (get_past_const (by trivial))]
    try simp only [←MLIR.run_nondet]
    rewrite [←MLIR.run_seq_def]
    rewrite[←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def]
    unfold opt4
    simp only

def opt_full : MLIRProgram := opt4
lemma opt_full_def : opt_full = opt4 := rfl
lemma optimised_behaviour_full :
  getReturn (full.runProgram st)  =
  getReturn (opt_full.runProgram st)  := by
  rewrite [optimised_behaviour4]
  rw [opt_full]
end Risc0.OneHot1.Constraints.Code