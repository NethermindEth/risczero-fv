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

elab "MLIR_old" : tactic => do
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

elab "MLIR_states_new" : tactic => do
  evalTactic <| ← `(tactic| simp [
    getImpl, isGetValid, Buffer.back, State.updateFelts, Option.get!,
    Buffer.get!, State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
    Option.isEqSome, List.set
  ])

-- private lemma run_set_enforce_aux {st : State} (h : val ∈ st.felts) :
--   Γ st ⟦buf[offset] ←ᵢ val⟧ = st.set! buf offset (st.felts[val].get h) := by
--   simp [State.update, MLIR.run]
--   rw [Map.mem_def, Map.getElem_def, Option.isSome_iff_exists] at h; rcases h with ⟨w, h⟩
--   simp [h]

-- private lemma run_set_enforce_aux! {st : State} (h : val ∈ st.felts) :
--   Γ st ⟦buf[offset] ←ᵢ val⟧ = st.set! buf offset st.felts[val].get! := by
--   simp [State.update, MLIR.run]
--   rw [Map.mem_def, Map.getElem_def, Option.isSome_iff_exists] at h; rcases h with ⟨w, h⟩
--   simp [h]

-- elab "MLIR_statement" : tactic => do
--   evalTactic <| ← `(
--     tactic| (
--       rewrite [MLIR.run_seq_def]
--       repeat (
--         first
--         | rewrite [MLIR.run_ass_def]
--         | (rewrite [run_set_enforce_aux!] <;> try decide_mem_map)
--         | rewrite [MLIR.run_if']
--         | rewrite [MLIR.run_nondet]
--         | rewrite [MLIR.run_eqz']
--       )
--       simp_op
--     )
--   )

elab "MLIR_statement" : tactic => do
  evalTactic <| ← `(
    tactic| (
      rewrite [MLIR.run_seq_def]
      repeat (
        first
        | rewrite [MLIR.run_ass_def]
        | rewrite [MLIR.run_set_def]
        | rewrite [MLIR.run_if]
        | rewrite [MLIR.run_nondet]
        | rewrite [MLIR.run_eqz]
      )
      simp_op
    )
  )

elab "MLIR" : tactic => do
  evalTactic <| ← `(
    tactic| repeat MLIR_statement
  )
  evalTactic <| ← `(tactic| try simp [Buffer.back_def.symm, isGetValid_def.symm, getImpl_def.symm, -zero_le, -zero_le', -Nat.zero_le])
  
-- elab "MLIR_statement" : tactic => do
--   evalTactic <| ← `(
--     tactic| (
--       rewrite [MLIR.run_seq_def]
--       repeat (
--         first
--         | rewrite [MLIR.run_ass_def]
--         | rewrite [MLIR.run_set_output]
--         | rewrite [MLIR.run_if]
--         | rewrite [MLIR.run_nondet]
--         | rewrite [MLIR.run_eqz]
--       )
--       simp_op
--     )
--   )

elab "MLIR_decide_updates" : tactic => do
  evalTactic <| ← `(tactic|
    simp only [
      Map.update, getElem!, ite_true, Option.get!_of_some, ite_false, true_and, Option.getD_some,
      State.updateFelts, Map.fromList_cons, Map.fromList_nil, State.update_val', 
      le_refl, List.find?, List.mem_cons, ge_iff_le, tsub_eq_zero_of_le,
      List.cons.injEq, and_imp, forall_apply_eq_imp_iff', forall_eq',
      Nat.succ_ne_self, IsEmpty.forall_iff, implies_true, forall_const, Nat.succ.injEq
    ])
  evalTactic <| ← `(tactic| simp only [Map.update_def.symm])

elab "MLIR_states_updates" : tactic => do
  evalTactic <| ← `(
    tactic| (MLIR_states_new; MLIR_decide_updates)
  )

end tactics

end Risc0
