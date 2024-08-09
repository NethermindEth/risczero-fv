import Risc0.Map
import Risc0.MlirTactics
import Risc0.Optimisation
import Risc0.Gadgets.OneHot1.Witness.Code

namespace Risc0.OneHot1.Witness.Code

open MLIRNotation

def opt1 : MLIRProgram :=
  "%1" ←ₐ .Const 0; "%2" ←ₐ .Get ⟨"code"⟩ 0 0; nondet ( "%8" ←ₐ ??₀⟨"%2"⟩; ⟨"data"⟩[0] ←ᵢ ⟨"%8"⟩ ); "%3" ←ₐ .Sub ⟨"%1"⟩ ⟨"%2"⟩; ?₀ ⟨"%3"⟩; "%4" ←ₐ .Get ⟨"data"⟩ 0 0; "%0" ←ₐ .Const 1; "%5" ←ₐ .Sub ⟨"%0"⟩ ⟨"%4"⟩; "%6" ←ₐ .Mul ⟨"%4"⟩ ⟨"%5"⟩; ?₀ ⟨"%6"⟩; "%7" ←ₐ .Sub ⟨"%4"⟩ ⟨"%0"⟩; ?₀ ⟨"%7"⟩
lemma optimised_behaviour1 :
  getReturn (full.runProgram st) res =
  getReturn (opt1.runProgram st) res := by
    unfold getReturn MLIR.runProgram full
    rewrite[opt_swap (const_past_const (by trivial)),opt_swap (const_past_get (by trivial)),opt_swap_nondet_seq (const_past_isz (by trivial) (by trivial)),opt_swap_nondet_single (const_past_set (by trivial)),opt_swap (const_past_sub (by trivial) (by trivial) (by trivial)),opt_swap (const_past_eqz (by trivial)),opt_swap (const_past_get (by trivial))]
    try simp only [←MLIR.run_nondet]
    rewrite [←MLIR.run_seq_def]
    rewrite[←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←step_nondet,←MLIR.run_seq_def,←MLIR.run_seq_def]
    unfold opt1
    simp only

def opt2 : MLIRProgram :=
  "%2" ←ₐ .Get ⟨"code"⟩ 0 0; nondet ( "%8" ←ₐ ??₀⟨"%2"⟩; ⟨"data"⟩[0] ←ᵢ ⟨"%8"⟩ ); "%1" ←ₐ .Const 0; "%3" ←ₐ .Sub ⟨"%1"⟩ ⟨"%2"⟩; ?₀ ⟨"%3"⟩; "%4" ←ₐ .Get ⟨"data"⟩ 0 0; "%0" ←ₐ .Const 1; "%5" ←ₐ .Sub ⟨"%0"⟩ ⟨"%4"⟩; "%6" ←ₐ .Mul ⟨"%4"⟩ ⟨"%5"⟩; ?₀ ⟨"%6"⟩; "%7" ←ₐ .Sub ⟨"%4"⟩ ⟨"%0"⟩; ?₀ ⟨"%7"⟩
lemma optimised_behaviour2 :
  getReturn (full.runProgram st) res =
  getReturn (opt2.runProgram st) res := by
    rewrite [optimised_behaviour1]
    unfold getReturn MLIR.runProgram opt1
    rewrite[opt_swap (const_past_get (by trivial)),opt_swap_nondet_seq (const_past_isz (by trivial) (by trivial)),opt_swap_nondet_single (const_past_set (by trivial))]
    try simp only [←MLIR.run_nondet]
    rewrite [←MLIR.run_seq_def]
    rewrite[←step_nondet,←MLIR.run_seq_def]
    unfold opt2
    simp only

def opt3 : MLIRProgram :=
  "%2" ←ₐ .Get ⟨"code"⟩ 0 0; nondet ( "%8" ←ₐ ??₀⟨"%2"⟩; ⟨"data"⟩[0] ←ᵢ ⟨"%8"⟩ ); "%1" ←ₐ .Const 0; "%3" ←ₐ .Sub ⟨"%1"⟩ ⟨"%2"⟩; ?₀ ⟨"%3"⟩; "%0" ←ₐ .Const 1; "%4" ←ₐ .Get ⟨"data"⟩ 0 0; "%5" ←ₐ .Sub ⟨"%0"⟩ ⟨"%4"⟩; "%6" ←ₐ .Mul ⟨"%4"⟩ ⟨"%5"⟩; ?₀ ⟨"%6"⟩; "%7" ←ₐ .Sub ⟨"%4"⟩ ⟨"%0"⟩; ?₀ ⟨"%7"⟩
lemma optimised_behaviour3 :
  getReturn (full.runProgram st) res =
  getReturn (opt3.runProgram st) res := by
    rewrite [optimised_behaviour2]
    unfold getReturn MLIR.runProgram opt2
    rewrite[MLIR.run_seq_def,step_nondet,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite[opt_swap (get_past_const (by trivial))]
    try simp only [←MLIR.run_nondet]
    rewrite [←MLIR.run_seq_def]
    rewrite[←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←step_nondet,←MLIR.run_seq_def]
    unfold opt3
    simp only

def opt_full : MLIRProgram := opt3
lemma opt_full_def : opt_full = opt3 := rfl
lemma optimised_behaviour_full :
  getReturn (full.runProgram st) res =
  getReturn (opt_full.runProgram st) res := by
  rewrite [optimised_behaviour3]
  rw [opt_full]
end Risc0.OneHot1.Witness.Code