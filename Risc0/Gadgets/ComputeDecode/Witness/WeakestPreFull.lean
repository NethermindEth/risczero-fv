import Risc0.Basic
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.CodeReordered
import Risc0.Gadgets.ComputeDecode.Witness.CodeParts
import Risc0.Gadgets.ComputeDecode.Witness.CodeDrops
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart0
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart1
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart2
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart3
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart4
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart5
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart6
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart7
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart8
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart9
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart10
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart11
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart12
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart13
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart14
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart15
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart16
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart17
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart18
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart19
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart20
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart21
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart22
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart23
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart24
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart25
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart26
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart27
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart28
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart29
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart30
-- import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart31

namespace Risc0.ComputeDecode.Witness.WP

def start_state (input : BufferAtTime) : State :=
  { buffers := Map.fromList [(⟨"in"⟩, [input]), (⟨"data"⟩, [[none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]])]
  , bufferWidths := Map.fromList [(⟨"in"⟩, 4), (⟨"data"⟩, 18)] --input width 128?
  , constraints := []
  , cycle := 0
  , felts := Map.empty
  , props := Map.empty
  , vars := [⟨"in"⟩, ⟨"data"⟩]
  , isFailed := false
  }

lemma closed_form {x₀ x₁ x₂ x₃: Felt} {y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ y₁₄ y₁₅ y₁₆ y₁₇ : Option Felt} :
  Code.run (start_state [x₀, x₁, x₂, x₃]) = [y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂, y₁₃, y₁₄, y₁₅, y₁₆, y₁₇ ] ↔ sorry := by
  unfold Code.run
  rewrite [Code.optimised_behaviour1]
  rewrite [Code.optimised_behaviour2]
  rewrite [Code.optimised_behaviour3]
  rewrite [Code.optimised_behaviour4]
  rewrite [Code.optimised_behaviour5]
  rewrite [Code.optimised_behaviour6]
  rewrite [Code.optimised_behaviour7]
  rewrite [Code.optimised_behaviour8]
  rewrite [Code.optimised_behaviour9]
  rewrite [Code.optimised_behaviour10]
  rewrite [Code.optimised_behaviour11]
  rewrite [Code.optimised_behaviour12]
  rewrite [Code.optimised_behaviour13]
  rewrite [Code.optimised_behaviour14]
  rewrite [Code.optimised_behaviour15]
  rewrite [Code.optimised_behaviour16]
  rewrite [Code.optimised_behaviour17]
  rewrite [Code.optimised_behaviour18]
  rewrite [Code.optimised_behaviour19]
  rewrite [Code.optimised_behaviour20]
  rewrite [Code.optimised_behaviour21]
  rewrite [Code.optimised_behaviour22]
  rewrite [Code.optimised_behaviour23]
  rewrite [Code.optimised_behaviour24]
  rewrite [Code.optimised_behaviour25]
  rewrite [Code.optimised_behaviour26]
  rewrite [Code.optimised_behaviour27]
  rewrite [Code.optimised_behaviour28]
  rewrite [Code.optimised_behaviour29]
  rewrite [Code.optimised_behaviour30]
  rewrite [Code.optimised_behaviour31]
  rewrite [Code.optimised_behaviour32]
  unfold MLIR.runProgram
  rewrite [←Code.parts_combine]
  unfold Code.parts_combined
  rewrite [←Code.getReturn_ignores_drops]
  rewrite [←Code.behaviour_with_drops]
  rewrite [part0_wp]
  rewrite [part1_updates_opaque]
  unfold start_state part0_state
  MLIR_states_updates

  rewrite [part2_updates_opaque]
  unfold part1_state
  MLIR_states_updates
  unfold part1_drops
  simp [State.dropFelts]
  MLIR_states_updates
  simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
  rewrite [Map.drop_of_updates]
  simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

  rewrite [part3_updates_opaque]
  unfold part2_state
  MLIR_states_updates
  unfold part2_drops
  simp [State.dropFelts]
  MLIR_states_updates
  simp only [ne_eq, Map.update_drop_swap, Map.update_drop, Map.drop_base]
  rewrite [Map.drop_of_updates]
  simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
  

  -- Code.run (start_state [x₀, x₁, x₂, x₃]) = [y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂, y₁₃, y₁₄, y₁₅, y₁₆, y₁₇ ] ↔ sorry := by
  -- rewrite [part0_wp]
  -- rewrite [part1_updates_opaque]
  -- unfold start_state
  -- unfold part0_state
  -- MLIR_states_updates

  -- rewrite [part2_updates_opaque]
  -- unfold part1_state
  -- MLIR_states_updates

  -- rewrite [part3_updates_opaque]
  -- unfold part2_state
  -- MLIR_states_updates

  -- rewrite [part4_updates_opaque]
  -- unfold part3_state
  -- MLIR_states_updates

  -- rewrite [part5_updates_opaque]
  -- unfold part4_state
  -- MLIR_states_updates

  -- rewrite [part6_updates_opaque]
  -- unfold part5_state
  -- MLIR_states_updates

  -- rewrite [part7_updates_opaque]
  -- unfold part6_state
  -- MLIR_states_updates


  -- generalize h_none : [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none] = nones

  -- -- rewrite [part8_updates_opaque]
  -- -- unfold part7_state
  -- -- MLIR_witness_updates

  -- -- rewrite [part9_updates_opaque]
  -- -- unfold part8_state
  -- -- MLIR_witness_updates

  -- -- rewrite [part₃_updates_opaque]
  -- -- rewrite [part₄_updates_opaque]
  -- -- rewrite [part₅_updates_opaque]



  -- -- unfold part₁_state
  -- -- MLIR_witness_updates

  -- -- unfold part₂_state
  -- -- MLIR_witness_updates

  -- -- unfold part₃_state
  -- -- MLIR_witness_updates

  -- -- unfold part₄_state
  -- -- MLIR_witness_updates

  -- -- unfold part₅_state
  -- -- MLIR_witness_updates

  -- -- simp [State.lastOutput, Option.get!, List.getLast!, List.getLast, State.buffers]
  -- -- MLIR_witness_updates
  -- -- simp [List.getLast]

end Risc0.ComputeDecode.Witness.WP
