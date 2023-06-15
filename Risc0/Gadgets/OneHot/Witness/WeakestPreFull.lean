import Risc0.Gadgets.OneHot.Witness.Code
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart0
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart8

namespace Risc0.OneHot.WP.Witness

def start_state (input: Felt) (st: State) :=
  st.WellFormed ∧
  (st.buffers.get! ⟨"input"⟩).last! = [some input] ∧
  (st.buffers.get! ⟨"output"⟩).last! = [none, none, none]

lemma closed_form {st: State} {input: Felt} {output₀ output₁ output₂ : Option Felt} :
  start_state input st → (
    Code.Witness.run st = [output₀, output₁, output₂] ↔ sorry
  ) := by
  unfold start_state
  intro h_pre
  unfold Code.Witness.run MLIR.runProgram; simp only [Code.Witness.parts_combine]
  rewrite [part₀_updates]
  rewrite [part₁_updates_opaque]
  rewrite [part₂_updates_opaque]
  rewrite [part₃_updates_opaque]
  rewrite [part₄_updates_opaque]
  rewrite [part₅_updates_opaque]
  rewrite [part₆_updates_opaque]
  rewrite [part₇_updates_opaque]
  rewrite [part₈_updates_opaque]

  unfold part₀_state
  simp [
    State.updateFelts, Map.get!, Option.get!, Buffer.get!,
    State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
    Option.isEqSome, List.set
  ]
  MLIR_states_simple; simp only [Map.update_def.symm]

  unfold part₁_state
  simp [
    State.updateFelts, Map.get!, Option.get!, Buffer.get!,
    State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
    Option.isEqSome, List.set
  ]
  MLIR_states_simple; simp only [Map.update_def.symm]

  unfold part₂_state
  simp [
    State.updateFelts, Map.get!, Option.get!, Buffer.get!,
    State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
    Option.isEqSome, List.set
  ]
  MLIR_states_simple; simp only [Map.update_def.symm]

  unfold part₃_state
  simp [
    State.updateFelts, Map.get!, Option.get!, Buffer.get!,
    State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
    Option.isEqSome, List.set
  ]
  MLIR_states_simple; simp only [Map.update_def.symm]

  unfold part₄_state
  simp [
    State.updateFelts, Map.get!, Option.get!, Buffer.get!,
    State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
    Option.isEqSome, List.set
  ]
  MLIR_states_simple; simp only [Map.update_def.symm]

  unfold part₅_state
  simp [
    State.updateFelts, Map.get!, Option.get!, Buffer.get!,
    State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
    Option.isEqSome, List.set
  ]
  MLIR_states_simple; simp only [Map.update_def.symm]

  unfold part₆_state
  simp [
    State.updateFelts, Map.get!, Option.get!, Buffer.get!,
    State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
    Option.isEqSome, List.set
  ]
  MLIR_states_simple; simp only [Map.update_def.symm]

  unfold part₇_state
  simp [
    State.updateFelts, Map.get!, Option.get!, Buffer.get!,
    State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
    Option.isEqSome, List.set
  ]
  MLIR_states_simple; simp only [Map.update_def.symm]

  unfold part₈_state
  simp [
    State.updateFelts, Map.get!, Option.get!, Buffer.get!,
    State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
    Option.isEqSome, List.set
  ]
  MLIR_states_simple; simp only [Map.update_def.symm]

  MLIR_states_simple; simp only [Map.update_def.symm]

  rw [State.felts_if] <;> try rfl
  simp [State.felts]
  MLIR_states_simple; simp only [Map.update_def.symm]

  rw [State.buffers_if] <;> try rfl
  simp [State.buffers]
  MLIR_states_simple; simp only [Map.update_def.symm]

  rw [State.bufferWidths_if] <;> try rfl
  simp [State.bufferWidths]
  MLIR_states_simple; simp only [Map.update_def.symm]

  rw [State.cycle_if] <;> try rfl
  simp [State.cycle]
  MLIR_states_simple; simp only [Map.update_def.symm]

  rw [State.isFailed_if] <;> try rfl
  simp [State.isFailed]
  MLIR_states_simple; simp only [Map.update_def.symm]

  rw [State.props_if] <;> try rfl
  simp [State.props]
  MLIR_states_simple; simp only [Map.update_def.symm]

  rw [State.vars_if] <;> try rfl
  simp [State.vars]
  MLIR_states_simple; simp only [Map.update_def.symm]

  simp [State.lastOutput, Option.get!, List.getLast!, List.getLast, State.buffers]
  
  rw [State.buffers_if] <;> try rfl
  simp [State.buffers]
  MLIR_states_simple; simp only [Map.update_def.symm]

  simp [List.getLast]

end Risc0.OneHot.WP.Witness