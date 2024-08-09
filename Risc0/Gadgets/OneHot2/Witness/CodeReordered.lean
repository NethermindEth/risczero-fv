import Risc0.Map
import Risc0.MlirTactics
import Risc0.Optimisation
import Risc0.Gadgets.OneHot2.Witness.Code

namespace Risc0.OneHot2.Witness.Code

open MLIRNotation

def opt1 : MLIRProgram :=
  "%1" ←ₐ .Const 0; "%2" ←ₐ .Get ⟨"code"⟩ 0 0; nondet ( "%12" ←ₐ ??₀⟨"%2"⟩; ⟨"data"⟩[0] ←ᵢ ⟨"%12"⟩ ); "%0" ←ₐ .Const 1; nondet ( "%13" ←ₐ .Sub ⟨"%2"⟩ ⟨"%0"⟩; "%14" ←ₐ ??₀⟨"%13"⟩; ⟨"data"⟩[1] ←ᵢ ⟨"%14"⟩ ); "%3" ←ₐ .Get ⟨"data"⟩ 0 1; "%4" ←ₐ .Sub ⟨"%3"⟩ ⟨"%2"⟩; ?₀ ⟨"%4"⟩; "%5" ←ₐ .Get ⟨"data"⟩ 0 0; "%6" ←ₐ .Sub ⟨"%0"⟩ ⟨"%5"⟩; "%7" ←ₐ .Mul ⟨"%5"⟩ ⟨"%6"⟩; ?₀ ⟨"%7"⟩; "%8" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%9" ←ₐ .Mul ⟨"%3"⟩ ⟨"%8"⟩; ?₀ ⟨"%9"⟩; "%10" ←ₐ .Add ⟨"%5"⟩ ⟨"%3"⟩; "%11" ←ₐ .Sub ⟨"%10"⟩ ⟨"%0"⟩; ?₀ ⟨"%11"⟩
lemma optimised_behaviour1 :
  getReturn (full.runProgram st) res =
  getReturn (opt1.runProgram st) res := by
    unfold getReturn MLIR.runProgram full
    rewrite[opt_swap (const_past_const (by trivial)),opt_swap (const_past_get (by trivial)),opt_swap_nondet_seq (const_past_isz (by trivial) (by trivial)),opt_swap_nondet_seq (const_past_set (by trivial))]
    try simp only [←MLIR.run_nondet]
    rewrite [←MLIR.run_seq_def]
    rewrite[←step_nondet,←MLIR.run_seq_def,←MLIR.run_seq_def]
    unfold opt1
    simp only

def opt2 : MLIRProgram :=
  "%2" ←ₐ .Get ⟨"code"⟩ 0 0; nondet ( "%12" ←ₐ ??₀⟨"%2"⟩; ⟨"data"⟩[0] ←ᵢ ⟨"%12"⟩ ); "%0" ←ₐ .Const 1; nondet ( "%13" ←ₐ .Sub ⟨"%2"⟩ ⟨"%0"⟩; "%14" ←ₐ ??₀⟨"%13"⟩; ⟨"data"⟩[1] ←ᵢ ⟨"%14"⟩ ); "%3" ←ₐ .Get ⟨"data"⟩ 0 1; "%4" ←ₐ .Sub ⟨"%3"⟩ ⟨"%2"⟩; ?₀ ⟨"%4"⟩; "%5" ←ₐ .Get ⟨"data"⟩ 0 0; "%6" ←ₐ .Sub ⟨"%0"⟩ ⟨"%5"⟩; "%7" ←ₐ .Mul ⟨"%5"⟩ ⟨"%6"⟩; ?₀ ⟨"%7"⟩; "%8" ←ₐ .Sub ⟨"%0"⟩ ⟨"%3"⟩; "%9" ←ₐ .Mul ⟨"%3"⟩ ⟨"%8"⟩; ?₀ ⟨"%9"⟩; "%10" ←ₐ .Add ⟨"%5"⟩ ⟨"%3"⟩; "%11" ←ₐ .Sub ⟨"%10"⟩ ⟨"%0"⟩; "%1" ←ₐ .Const 0; ?₀ ⟨"%11"⟩
lemma optimised_behaviour2 :
  getReturn (full.runProgram st) res =
  getReturn (opt2.runProgram st) res := by
    rewrite [optimised_behaviour1]
    unfold getReturn MLIR.runProgram opt1
    rewrite[opt_swap (const_past_get (by trivial)),opt_swap_nondet_seq (const_past_isz (by trivial) (by trivial)),opt_swap_nondet_single (const_past_set (by trivial)),opt_swap (const_past_const (by trivial)),opt_swap_nondet_seq (const_past_sub (by trivial) (by trivial) (by trivial)),opt_swap_nondet_seq (const_past_isz (by trivial) (by trivial)),opt_swap_nondet_single (const_past_set (by trivial)),opt_swap (const_past_get (by trivial)),opt_swap (const_past_sub (by trivial) (by trivial) (by trivial)),opt_swap (const_past_eqz (by trivial)),opt_swap (const_past_get (by trivial)),opt_swap (const_past_sub (by trivial) (by trivial) (by trivial)),opt_swap (const_past_mul (by trivial) (by trivial) (by trivial)),opt_swap (const_past_eqz (by trivial)),opt_swap (const_past_sub (by trivial) (by trivial) (by trivial)),opt_swap (const_past_mul (by trivial) (by trivial) (by trivial)),opt_swap (const_past_eqz (by trivial)),opt_swap (const_past_add (by trivial) (by trivial) (by trivial)),opt_swap (const_past_sub (by trivial) (by trivial) (by trivial))]
    try simp only [←MLIR.run_nondet]
    rewrite [←MLIR.run_seq_def]
    rewrite[←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←step_nondet,←step_nondet,←MLIR.run_seq_def,←MLIR.run_seq_def,←step_nondet,←MLIR.run_seq_def]
    unfold opt2
    simp only

def opt_full : MLIRProgram := opt2
lemma opt_full_def : opt_full = opt2 := rfl
lemma optimised_behaviour_full :
  getReturn (full.runProgram st) res =
  getReturn (opt_full.runProgram st) res := by
  rewrite [optimised_behaviour2]
  rw [opt_full]
end Risc0.OneHot2.Witness.Code