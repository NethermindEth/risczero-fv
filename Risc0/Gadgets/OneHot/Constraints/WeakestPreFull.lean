import Risc0.Gadgets.OneHot.Constraints.Code
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart0
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart1
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart2
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart3
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart4
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart5
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart6

namespace Risc0.OneHot.Constraints.WP

lemma closed_form {st: State} : Code.run st ↔ sorry := by
  sorry
  -- rewrite [part₀_wp]
  -- rewrite [part₁_updates_opaque]
  -- rewrite [part₂_updates_opaque]
  -- rewrite [part₃_updates_opaque]
  -- rewrite [part₄_updates_opaque]
  -- rewrite [part₅_updates_opaque]
  -- rewrite [part₆_updates_opaque]

  -- unfold part₀_state
  -- simp [
  --   State.updateFelts, Map.get!, Option.get!, Buffer.get!,
  --   State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
  --   Option.isEqSome, List.set
  -- ]
  -- MLIR_states_simple; simp only [Map.update_def.symm]

  -- unfold part₁_state
  -- simp [
  --   State.updateFelts, Map.get!, Option.get!, Buffer.get!,
  --   State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
  --   Option.isEqSome, List.set
  -- ]
  -- MLIR_states_simple; simp only [Map.update_def.symm]

  -- unfold part₂_state
  -- simp [
  --   State.updateFelts, Map.get!, Option.get!, Buffer.get!,
  --   State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
  --   Option.isEqSome, List.set
  -- ]
  -- MLIR_states_simple; simp only [Map.update_def.symm]

  -- unfold part₃_state
  -- simp [
  --   State.updateFelts, Map.get!, Option.get!, Buffer.get!,
  --   State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
  --   Option.isEqSome, List.set
  -- ]
  -- MLIR_states_simple; simp only [Map.update_def.symm]

  -- unfold part₄_state
  -- simp [
  --   State.updateFelts, Map.get!, Option.get!, Buffer.get!,
  --   State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
  --   Option.isEqSome, List.set
  -- ]
  -- MLIR_states_simple; simp only [Map.update_def.symm]

  -- unfold part₅_state
  -- simp [
  --   State.updateFelts, Map.get!, Option.get!, Buffer.get!,
  --   State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
  --   Option.isEqSome, List.set
  -- ]
  -- MLIR_states_simple; simp only [Map.update_def.symm]

  -- unfold part₆_state_update part₆_state
  -- simp [
  --   State.updateFelts, Map.get!, Option.get!, Buffer.get!,
  --   State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
  --   Option.isEqSome, List.set
  -- ]
  -- MLIR_states_simple; simp only [Map.update_def.symm]

  -- MLIR_states_simple; simp only [Map.update_def.symm]

  -- rw [State.felts_if] <;> try rfl
  -- simp [State.felts]
  -- MLIR_states_simple; simp only [Map.update_def.symm]

  -- rw [State.buffers_if] <;> try rfl
  -- simp [State.buffers]
  -- MLIR_states_simple; simp only [Map.update_def.symm]

  -- rw [State.bufferWidths_if] <;> try rfl
  -- simp [State.bufferWidths]
  -- MLIR_states_simple; simp only [Map.update_def.symm]

  -- rw [State.cycle_if] <;> try rfl
  -- simp [State.cycle]
  -- MLIR_states_simple; simp only [Map.update_def.symm]

  -- rw [State.isFailed_if] <;> try rfl
  -- simp [State.isFailed]
  -- MLIR_states_simple; simp only [Map.update_def.symm]

  -- rw [State.props_if] <;> try rfl
  -- simp [State.props]
  -- MLIR_states_simple; simp only [Map.update_def.symm]

  -- rw [State.vars_if] <;> try rfl
  -- simp [State.vars]
  -- MLIR_states_simple; simp only [Map.update_def.symm]

  -- simp [State.lastOutput, Option.get!, List.getLast!, List.getLast, State.buffers]
  
  -- rw [State.buffers_if] <;> try rfl
  -- simp [State.buffers]
  -- MLIR_states_simple; simp only [Map.update_def.symm]

  -- simp [List.getLast]

end Risc0.OneHot.Constraints.WP
