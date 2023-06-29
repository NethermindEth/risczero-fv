import Risc0.Gadgets.OneHot.Witness.Code
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart0
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart1
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart2
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart3
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart4
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart5
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart6
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart7
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart8

namespace Risc0.OneHot.Witness.WP

def start_state (input: Felt) : State :=
  { buffers := Map.fromList [(⟨"input"⟩, [[.some input]]), (⟨"output"⟩, [[none, none, none]])]
  , bufferWidths := Map.fromList [(⟨"input"⟩, 1), (⟨"output"⟩, 3)]
  , constraints := []
  , cycle := 0
  , felts := Map.empty
  , props := Map.empty
  , vars := [⟨"input"⟩, ⟨"output"⟩]
  , isFailed := false
  }

lemma closed_form {x : Felt} {y₁ y₂ y₃ : Option Felt} :
  Code.run (start_state x) = [y₁, y₂, y₃] ↔ sorry := by
  sorry --maximum recursion depth reached
  -- rewrite [part₀_wp]
  -- rewrite [part₁_updates_opaque]
  -- rewrite [part₂_updates_opaque]
  -- rewrite [part₃_updates_opaque]
  -- rewrite [part₄_updates_opaque]
  -- rewrite [part₅_updates_opaque]
  -- rewrite [part₆_updates_opaque]
  -- rewrite [part₇_updates_opaque]
  -- rewrite [part₈_updates_opaque]

  -- unfold start_state

  -- unfold part₀_state
  -- MLIR_states_updates

  -- unfold part₁_state
  -- MLIR_states_updates

  -- unfold part₂_state
  -- MLIR_states_updates

  -- unfold part₃_state
  -- MLIR_states_updates

  -- unfold part₄_state
  -- MLIR_states_updates

  -- unfold part₅_state
  -- MLIR_states_updates

  -- unfold part₆_state
  -- MLIR_states_updates

  -- unfold part₇_state
  -- MLIR_states_updates

  -- unfold part₈_state
  -- MLIR_states_updates

  -- simp [State.lastOutput, Option.get!, List.getLast!, List.getLast, State.buffers]
  -- MLIR_states_updates
  -- simp [List.getLast]

end Risc0.OneHot.Witness.WP
