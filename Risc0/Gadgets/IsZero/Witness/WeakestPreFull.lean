import Risc0.Gadgets.IsZero.Witness.Code
import Risc0.Gadgets.IsZero.Witness.WeakestPresPart0
import Risc0.Gadgets.IsZero.Witness.WeakestPresPart1
import Risc0.Gadgets.IsZero.Witness.WeakestPresPart2
import Risc0.Gadgets.IsZero.Witness.WeakestPresPart3
import Risc0.Gadgets.IsZero.Witness.WeakestPresPart4
import Risc0.Gadgets.IsZero.Witness.WeakestPresPart5

namespace Risc0.IsZero.Witness.WP

def start_state (input: Felt) : State :=
  { buffers := Map.fromList [(⟨"input"⟩, [[.some input]]), (⟨"output"⟩, [[none, none]])]
  , bufferWidths := Map.fromList [(⟨"input"⟩, 1), (⟨"output"⟩, 2)]
  , constraints := []
  , cycle := 0
  , felts := Map.empty
  , props := Map.empty
  , vars := [⟨"input"⟩, ⟨"output"⟩]
  , isFailed := false
  }


lemma closed_form {x : Felt} {y₁ y₂ : Option Felt} :
  Code.run (start_state x) = [y₁, y₂] ↔ (.some (if x = 0 then 1 else 0)) = y₁ ∧ (if x = 0 then 0 else x⁻¹) = y₂ := by
  rewrite [part₀_wp]
  rewrite [part₁_updates_opaque]
  rewrite [part₂_updates_opaque]
  rewrite [part₃_updates_opaque]
  rewrite [part₄_updates_opaque]
  rewrite [part₅_updates_opaque]

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

  simp [State.lastOutput, Option.get!, List.getLast!, List.getLast, State.buffers]
  MLIR_states_updates
  simp [List.getLast]

end Risc0.IsZero.Witness.WP