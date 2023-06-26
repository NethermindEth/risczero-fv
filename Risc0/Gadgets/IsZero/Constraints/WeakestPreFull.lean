import Risc0.Gadgets.IsZero.Constraints.Code
import Risc0.Gadgets.IsZero.Constraints.WeakestPresPart0
import Risc0.Gadgets.IsZero.Constraints.WeakestPresPart1
import Risc0.Gadgets.IsZero.Constraints.WeakestPresPart2
import Risc0.Gadgets.IsZero.Constraints.WeakestPresPart3
import Risc0.Gadgets.IsZero.Constraints.WeakestPresPart4

namespace Risc0.IsZero.Constraints.WP

def start_state (input : Felt) (output : BufferAtTime) : State :=
  { buffers := Map.fromList [(⟨Input⟩, [[.some input]]), (⟨Output⟩, [output])]
  , bufferWidths := Map.fromList [(⟨Input⟩, 1), (⟨Output⟩, 2)]
  , constraints := []
  , cycle := 0
  , felts := Map.empty
  , props := Map.empty
  , vars := [⟨Input⟩, ⟨Output⟩]
  , isFailed := false
  }

lemma closed_form {x: Felt} {y₁ y₂ : Felt} : Code.run (start_state x ([some y₁, some y₂])) ↔
    (if y₁ = 0 then True else x = 0) ∧ if 1 - y₁ = 0 then True else x * y₂ - 1 = 0 := by
  rw [part₀_wp]
  rw [part₁_updates_opaque]
  rw [part₂_updates_opaque]
  rw [part₃_updates_opaque]
  rw [part₄_updates_opaque]

  generalize eq : ((if y₁ = 0 then True else x = 0) ∧ if 1 - y₁ = 0 then True else x * y₂ - 1 = 0) = rhs

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

  simp [Code.getReturn, State.constraintsInVar, State.constraints]
  rw [←eq]

end Risc0.IsZero.Constraints.WP
