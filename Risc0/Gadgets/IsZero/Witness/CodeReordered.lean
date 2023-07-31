import Risc0.Map
import Risc0.MlirTactics
import Risc0.Optimisation
import Risc0.Gadgets.IsZero.Witness.Code

namespace Risc0.IsZero.Witness.Code

open MLIRNotation

def opt1 : MLIRProgram :=
  "%1" ←ₐ .Get ⟨"in"⟩ 0 0; nondet ( "%4" ←ₐ ??₀⟨"%1"⟩; ⟨"data"⟩[0] ←ᵢ ⟨"%4"⟩; "%5" ←ₐ Inv⟨"%1"⟩; ⟨"data"⟩[1] ←ᵢ ⟨"%5"⟩ ); "%2" ←ₐ .Get ⟨"data"⟩ 0 0; guard ⟨"%2"⟩ then (?₀ ⟨"%1"⟩); "%0" ←ₐ .Const 1; "%3" ←ₐ .Sub ⟨"%0"⟩ ⟨"%2"⟩; guard ⟨"%3"⟩ then ("%4" ←ₐ .Get ⟨"data"⟩ 0 1; "%5" ←ₐ .Mul ⟨"%1"⟩ ⟨"%4"⟩; "%6" ←ₐ .Sub ⟨"%5"⟩ ⟨"%0"⟩; ?₀ ⟨"%6"⟩)
lemma optimised_behaviour1 :
  getReturn (full.runProgram st) =
  getReturn (opt1.runProgram st) := by
    unfold getReturn MLIR.runProgram full
    rewrite[opt_swap (const_past_get (by trivial)),opt_swap_nondet_seq (const_past_isz (by trivial) (by trivial)),opt_swap_nondet_seq (const_past_set (by trivial)),opt_swap_nondet_seq (const_past_inv (by trivial) (by trivial)),opt_swap_nondet_single (const_past_set (by trivial)),opt_swap (const_past_get (by trivial)),opt_swap (const_past_if  (by trivial) (const_past_eqz (by trivial)))]
    simp only [←MLIR.run_nondet]
    rewrite [←MLIR.run_seq_def]
    rewrite[←MLIR.run_seq_def,←MLIR.run_seq_def,←step_nondet,←step_nondet,←step_nondet,←MLIR.run_seq_def]
    apply optim_rfl_hic_sunt_dracones
    unfold opt1
    with_reducible rfl

def opt_full : MLIRProgram := opt1
lemma opt_full_def : opt_full = opt1 := rfl
lemma optimised_behaviour_full :
  getReturn (full.runProgram st) =
  getReturn (opt_full.runProgram st) := by
  rewrite [optimised_behaviour1]
  rw [opt_full]
end Risc0.IsZero.Witness.Code