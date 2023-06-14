import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp

import Risc0.Basic
import Risc0.Lemmas
import Risc0.Wheels

namespace Risc0

section tactics

open Lean Elab Tactic

open Op in
elab "simp_op" : tactic => do
  evalTactic <| ← `( tactic|
    simp only [
      eval_const, eval_true, eval_getBuffer, eval_sub,
      eval_mul, eval_isz, eval_inv, eval_andEqz, eval_andCond
    ]
  )

elab "MLIR" : tactic => do
  evalTactic <| ← `(
    tactic| repeat ( first |
      rw [MLIR.run_ass_def] | rw [MLIR.run_set_output] | rw [MLIR.run_if] |
      rw [MLIR.run_nondet] | rw [MLIR.run_eqz] |
      rw [MLIR.run_seq_def] 
      all_goals try rfl
      simp_op
    )
  )
  evalTactic <| ← `(tactic| try rw [MLIR.run_ass_def])
  evalTactic <| ← `(tactic| simp)

elab "MLIR_state" : tactic => do
  evalTactic <| ← `(tactic| repeat rw [Map.update_get_skip])
  evalTactic <| ← `(tactic| all_goals try decide)
  evalTactic <| ← `(tactic| all_goals try rfl)
  evalTactic <| ← `(tactic| all_goals simp only)
  -- evalTactic <| ← `(tactic| simp)

elab "MLIR_states" : tactic => do
  evalTactic <| ← `(tactic| repeat MLIR_state)

elab "MLIR_statement" : tactic => do
  evalTactic <| ← `(tactic| rewrite [MLIR.run_seq_def])
  evalTactic <| ← `(
    tactic| repeat ( first
      | rw [MLIR.run_ass_def]
      | rw [MLIR.run_set_output]
      | rw [MLIR.run_if]
      | rw [MLIR.run_nondet]
      | rw [MLIR.run_eqz]
    )
  )

end tactics

end Risc0
