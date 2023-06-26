import Risc0.Gadgets.OneHot.Constraints.Code
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart0
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart1
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart2
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart3
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart4
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart5
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart6

namespace Risc0.OneHot.Constraints.WP

def start_state (input : Felt) (output : BufferAtTime) : State :=
  { buffers := Map.fromList [(⟨"input"⟩, [[.some input]]), (⟨"output"⟩, [output])]
  , bufferWidths := Map.fromList [(⟨"input"⟩, 1), (⟨"output"⟩, 3)]
  , constraints := []
  , cycle := 0
  , felts := Map.empty
  , props := Map.empty
  , vars := [⟨"input"⟩, ⟨"output"⟩]
  , isFailed := false
  }

lemma closed_form {x: Felt} {y₁ y₂ y₃ : Felt} : Code.run (start_state x ([some y₁, some y₂, some y₃])) ↔
    ((y₂ + y₃ * 2 - x = 0 ∧ (y₁ = 0 ∨ 1 - y₁ = 0)) ∧ (y₂ = 0 ∨ 1 - y₂ = 0)) ∧ y₁ + y₂ + y₃ - 1 = 0 := by
  rw [part₀_wp]
  rw [part₁_updates_opaque]
  rw [part₂_updates_opaque]
  rw [part₃_updates_opaque]
  rw [part₄_updates_opaque]
  rw [part₅_updates_opaque]
  rw [part₆_updates_opaque]

  generalize eq : (((y₂ + y₃ * 2 - x = 0 ∧ (y₁ = 0 ∨ 1 - y₁ = 0)) ∧ (y₂ = 0 ∨ 1 - y₂ = 0)) ∧ y₁ + y₂ + y₃ - 1 = 0) = rhs

  unfold start_state

  unfold part₀_state
  MLIR_states_updates

  unfold part₁_state
  MLIR_states_updates
  
  unfold part₂_state
  MLIR_states_updates

  unfold part₃_state
  MLIR_states_updates

  unfold part₄_state
  MLIR_states_updates

  unfold part₅_state
  MLIR_states_updates

  unfold part₆_state
  MLIR_states_updates

  simp only [Code.getReturn, State.constraintsInVar, State.updateProps_props_get_wobbly, Option.getD_some]
  rw [←eq]

end Risc0.OneHot.Constraints.WP
