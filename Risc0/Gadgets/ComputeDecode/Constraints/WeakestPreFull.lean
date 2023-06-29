import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart0
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart1
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart2
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart3
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart4
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart5
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart6
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart7
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart8
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart9
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart10
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart11
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart12
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart13
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart14
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart15
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart16

namespace Risc0.ComputeDecode.Constraints.WP

def start_state (input : BufferAtTime) (data : BufferAtTime) : State :=
  { buffers := Map.fromList [(⟨"in"⟩, [input]), (⟨"data"⟩, [data])]
  , bufferWidths := Map.fromList [(⟨"in"⟩, 4), (⟨"data"⟩, 18)] --input width 128?
  , constraints := []
  , cycle := 0
  , felts := Map.empty
  , props := Map.empty
  , vars := [⟨"in"⟩, ⟨"data"⟩]
  , isFailed := false
  }

lemma closed_form {x₀ x₁ x₂ x₃: Felt} {y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ y₁₄ y₁₅ y₁₆ y₁₇ : Felt} :
  Code.run (start_state
    [some x₀, some x₁, some x₂, some x₃] ([some y₀, some y₁, some y₂, some y₃, some y₄, some y₅, some y₆, some y₇, some y₈, some y₉, some y₁₀, some y₁₁, some y₁₂, some y₁₃, some y₁₄, some y₁₅, some y₁₆, some y₁₇])) ↔
    ((x₃ - ((y₁₀ * 64 + (y₁ * 16 + y₉ * 8 + y₈ * 4 + y₀)) * 2 + y₁₃) = 0 ∧
        x₂ - ((y₁₂ * 8 + y₂ * 2 + y₁₁) * 16 + y₄ * 4 + y₃) = 0) ∧
      x₁ - (y₁₄ * 128 + (y₁₅ * 4 + y₅) * 16 + y₇ * 4 + y₆) = 0) ∧
    x₀ - (y₁₆ * 128 + y₁₇) = 0 := by
  rw [part0_wp]
  rw [part1_updates_opaque]
  rw [part2_updates_opaque]
  rw [part3_updates_opaque]
  rw [part4_updates_opaque]
  rw [part5_updates_opaque]
  rw [part6_updates_opaque]
  rw [part7_updates_opaque]
  rw [part8_updates_opaque]
  rw [part9_updates_opaque]
  rw [part10_updates_opaque]
  rw [part11_updates_opaque]
  rw [part12_updates_opaque]
  rw [part13_updates_opaque]
  rw [part14_updates_opaque]
  rw [part15_updates_opaque]
  rw [part16_updates_opaque]

  generalize eq : (((x₃ - ((y₁₀ * 64 + (y₁ * 16 + y₉ * 8 + y₈ * 4 + y₀)) * 2 + y₁₃) = 0 ∧
        x₂ - ((y₁₂ * 8 + y₂ * 2 + y₁₁) * 16 + y₄ * 4 + y₃) = 0) ∧
      x₁ - (y₁₄ * 128 + (y₁₅ * 4 + y₅) * 16 + y₇ * 4 + y₆) = 0) ∧
    x₀ - (y₁₆ * 128 + y₁₇) = 0) = rhs

  unfold start_state

  unfold part0_state
  MLIR_states_updates

  unfold part1_state
  MLIR_states_updates
  
  unfold part2_state
  MLIR_states_updates

  unfold part3_state
  MLIR_states_updates

  unfold part4_state
  MLIR_states_updates

  unfold part5_state
  MLIR_states_updates

  unfold part6_state
  MLIR_states_updates

  unfold part7_state
  MLIR_states_updates

  unfold part8_state
  MLIR_states_updates

  unfold part9_state
  MLIR_states_updates

  unfold part10_state
  MLIR_states_updates

  unfold part11_state
  MLIR_states_updates

  unfold part12_state
  MLIR_states_updates

  unfold part13_state
  MLIR_states_updates

  unfold part14_state
  MLIR_states_updates

  unfold part15_state
  MLIR_states_updates

  unfold part16_state
  MLIR_states_updates

  simp only [Code.getReturn, State.constraintsInVar, State.updateProps_props_get_wobbly, Option.getD_some]
  rw [←eq]

end Risc0.ComputeDecode.Constraints.WP
