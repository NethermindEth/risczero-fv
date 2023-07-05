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
      eval_const, eval_true, eval_getBuffer, eval_add, eval_sub,
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
    getImpl, isGetValid, Buffer.back, Option.get!,
    Buffer.get!, State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
    Option.isEqSome, List.set, State.felts_if, State.buffers_if, State.bufferWidths_if,
    State.cycle_if, State.isFailed_if, State.vars_if, State.props_if,
    State.constraints_if, State.props_if
  ])

elab "MLIR_states_new?" : tactic => do
  evalTactic <| ← `(tactic| simp? [
    getImpl, isGetValid, Buffer.back, Option.get!,
    Buffer.get!, State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
    Option.isEqSome, List.set, State.felts_if, State.buffers_if, State.bufferWidths_if,
    State.cycle_if, State.isFailed_if, State.vars_if, State.props_if,
    State.constraints_if, State.props_if
  ])

elab "MLIR_states_new'" : tactic => do
  evalTactic <| ← `(tactic| simp only [
    getImpl, isGetValid, Buffer.back, Option.get!,
    Buffer.get!, State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
    Option.isEqSome, List.set, State.felts_if, State.buffers_if, State.bufferWidths_if,
    State.cycle_if, State.isFailed_if, State.vars_if, State.props_if,
    State.constraints_if, State.props_if, Map.fromList_cons, Map.fromList_nil, getImpl, isGetValid, le_refl, List.find?, List.mem_cons,
    Option.get!, Buffer.back, Buffer.get!, List.get!, Option.isSome_some, and_true, true_and, ne_eq,
    State.updateFelts_props, State.updateProps_props_get_wobbly,
    State.updateFelts_felts_get_wobbly, mul_eq_zero, State.updateFelts_felts_get_next, State.updateProps_felts
  ])

elab "MLIR_states_new'?" : tactic => do
  evalTactic <| ← `(tactic| simp? only [
    getImpl, isGetValid, Buffer.back, Option.get!,
    Buffer.get!, State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
    Option.isEqSome, List.set, State.felts_if, State.buffers_if, State.bufferWidths_if,
    State.cycle_if, State.isFailed_if, State.vars_if, State.props_if,
    State.constraints_if, State.props_if, Map.fromList_cons, Map.fromList_nil, getImpl, isGetValid, le_refl, List.find?, List.mem_cons,
    Option.get!, Buffer.back, Buffer.get!, List.get!, Option.isSome_some, and_true, true_and, ne_eq,
    State.updateFelts_props, State.updateProps_props_get_wobbly,
    State.updateFelts_felts_get_wobbly, mul_eq_zero, State.updateFelts_felts_get_next, State.updateProps_felts
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
      first 
      | rewrite [MLIR.run_nondet_seq_def]
      | rewrite [MLIR.run_seq_def]
      repeat (
        first
        | rewrite [MLIR.run_ass_def]
        | rewrite [MLIR.run_set_def]
        | rewrite [MLIR.run_if]
        | rewrite [MLIR.run_nondet]
        | rewrite [MLIR.run_eqz]
        | rewrite [MLIR.run_dropfelt]
      )
      simp_op
    )
  )

elab "MLIR_single" : tactic => do
  evalTactic <| ← `(
    tactic| (
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
  evalTactic <| ← `(tactic| try simp [Buffer.back_def.symm, isGetValid_def.symm, getImpl_def.symm, -zero_le, -zero_le', -Nat.zero_le])

elab "MLIR" : tactic => do
  evalTactic <| ← `(
    tactic| repeat MLIR_statement
  )
  evalTactic <| ← `(tactic| try simp [getImpl_skip_set_offset, Buffer.back_def.symm, isGetValid_def.symm, getImpl_def.symm, -zero_le, -zero_le', -Nat.zero_le])

elab "MLIR?" : tactic => do
  evalTactic <| ← `(
    tactic| repeat MLIR_statement
  )
  evalTactic <| ← `(tactic| try simp? [Buffer.back_def.symm, isGetValid_def.symm, getImpl_def.symm, -zero_le, -zero_le', -Nat.zero_le])
  
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
      Map.fromList_cons, Map.fromList_nil, State.update_val', 
      le_refl, List.find?, List.mem_cons, ge_iff_le, tsub_eq_zero_of_le,
      List.cons.injEq, and_imp, forall_apply_eq_imp_iff', forall_eq',
      Nat.succ_ne_self, IsEmpty.forall_iff, implies_true, forall_const, Nat.succ.injEq,
      getElem, instGetElemMapOptionTrue, State.updateFelts_buffers, State.updateFelts_bufferWidths,
      State.updateFelts_constraints, State.updateFelts_cycle, State.updateFelts_isFailed,
      State.updateFelts_props, State.updateFelts_vars, State.updateFelts_felts, State.updateProps_buffers,
      State.updateProps_bufferWidths, State.updateProps_constraints, State.updateProps_cycle,
      State.updateProps_isFailed, State.updateProps_felts, State.updateProps_vars, State.updateProps_props,
      State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars,
      withEqZero_buffers, withEqZero_bufferWidths, withEqZero_constraints, withEqZero_cycle, withEqZero_felts, withEqZero_isFailed, withEqZero_props, withEqZero_vars,
      getImpl_skip_set_offset
    ])
  evalTactic <| ← `(tactic| simp only [Map.update_def.symm])

lemma getImpl_get_of_isGetValid {x : BufferVar} {st : State} (h : isGetValid st x m n) :
  getImpl st x m n = some (Lit.Val (Option.get! (Buffer.back st x m n))) := by
  simp [getImpl, h]

elab "MLIR_states_updates_hack" : tactic => do
  evalTactic <| ← `(
    tactic| (
      MLIR_states_new
      -- simp [←Map.getElem_def, Map.update_get_next, Map.update_get_next', Map.update_get]
      MLIR_decide_updates
    )
  )

open Lean Elab Tactic in
elab "simplify_get_hack" : tactic => do
  evalTactic <| ← `(
    tactic| (
      try (rewrite [getImpl_get_of_isGetValid]; swap; unfold isGetValid; MLIR_states_updates_hack)
    )
  )

elab "MLIR_states_updates" : tactic => do
  evalTactic <| ← `(
    tactic| (
      simplify_get_hack
      MLIR_states_new
      -- simp [←Map.getElem_def, Map.update_get_next, Map.update_get_next', Map.update_get]
      MLIR_decide_updates
    )
  )

elab "MLIR_states_updates?" : tactic => do
  evalTactic <| ← `(
    tactic| (
      MLIR_states_new?
      -- simp [←Map.getElem_def, Map.update_get_next, Map.update_get_next', Map.update_get]
      MLIR_decide_updates
    )
  )

elab "MLIR_states_updates'" : tactic => do
  evalTactic <| ← `(
    tactic| (
      MLIR_states_new'
      -- simp [←Map.getElem_def, Map.update_get_next, Map.update_get_next', Map.update_get]
      MLIR_decide_updates
    )
  )

elab "MLIR_states_updates'?" : tactic => do
  evalTactic <| ← `(
    tactic| (
      MLIR_states_new'?
      -- simp [←Map.getElem_def, Map.update_get_next, Map.update_get_next', Map.update_get]
      MLIR_decide_updates
    )
  )

end tactics

end Risc0
