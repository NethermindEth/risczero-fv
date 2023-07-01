import Risc0.Basic
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.CodeReordered
import Risc0.Gadgets.ComputeDecode.Witness.CodeParts
import Risc0.Gadgets.ComputeDecode.Witness.CodeDrops
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart0
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart1
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart2
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart3
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart4
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart5
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart6
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart7
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart8
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart9
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart10
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart11
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart12
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart13
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart14
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart15
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart16
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart17
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart18
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart19
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart20
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart21
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart22
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart23
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart24
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart25
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart26
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart27
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart28
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart29
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart30
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart31

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

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

lemma use_opt_full {x₀ x₁ x₂ x₃: Felt} :
  Code.run (start_state [x₀, x₁, x₂, x₃]) = 
  Code.getReturn (Γ (start_state [x₀, x₁, x₂, x₃]) ⟦Code.part0; Code.part1; dropfelt ⟨"%74"⟩; dropfelt ⟨"%75"⟩; Code.part2; dropfelt ⟨"%76"⟩; dropfelt ⟨"%77"⟩; Code.part3; dropfelt ⟨"%78"⟩; dropfelt ⟨"%79"⟩; Code.part4; dropfelt ⟨"%80"⟩; dropfelt ⟨"%12"⟩; Code.part5; dropfelt ⟨"%81"⟩; dropfelt ⟨"%10"⟩; Code.part6; dropfelt ⟨"%82"⟩; dropfelt ⟨"%9"⟩; dropfelt ⟨"%83"⟩; dropfelt ⟨"%8"⟩; Code.part7; dropfelt ⟨"%84"⟩; dropfelt ⟨"%85"⟩; Code.part8; dropfelt ⟨"%17"⟩; dropfelt ⟨"%16"⟩; dropfelt ⟨"%86"⟩; dropfelt ⟨"%87"⟩; dropfelt ⟨"%88"⟩; Code.part9; dropfelt ⟨"%89"⟩; dropfelt ⟨"%90"⟩; Code.part10; dropfelt ⟨"%91"⟩; dropfelt ⟨"%92"⟩; Code.part11; dropfelt ⟨"%93"⟩; Code.part12; dropfelt ⟨"%94"⟩; dropfelt ⟨"%95"⟩; Code.part13; dropfelt ⟨"%96"⟩; dropfelt ⟨"%2"⟩; dropfelt ⟨"%97"⟩; Code.part14; dropfelt ⟨"%14"⟩; dropfelt ⟨"%1"⟩; dropfelt ⟨"%98"⟩; dropfelt ⟨"%99"⟩; Code.part15; dropfelt ⟨"%6"⟩; dropfelt ⟨"%5"⟩; dropfelt ⟨"%4"⟩; dropfelt ⟨"%100"⟩; dropfelt ⟨"%101"⟩; Code.part16; dropfelt ⟨"%18"⟩; dropfelt ⟨"%102"⟩; dropfelt ⟨"%103"⟩; Code.part17; dropfelt ⟨"%104"⟩; dropfelt ⟨"%0"⟩; dropfelt ⟨"%105"⟩; Code.part18; dropfelt ⟨"%26"⟩; Code.part19; dropfelt ⟨"%28"⟩; dropfelt ⟨"%29"⟩; dropfelt ⟨"%30"⟩; dropfelt ⟨"%31"⟩; Code.part20; dropfelt ⟨"%27"⟩; dropfelt ⟨"%32"⟩; dropfelt ⟨"%33"⟩; dropfelt ⟨"%25"⟩; Code.part21; dropfelt ⟨"%3"⟩; dropfelt ⟨"%34"⟩; dropfelt ⟨"%35"⟩; dropfelt ⟨"%36"⟩; dropfelt ⟨"%37"⟩; Code.part22; dropfelt ⟨"%23"⟩; dropfelt ⟨"%38"⟩; dropfelt ⟨"%24"⟩; dropfelt ⟨"%39"⟩; dropfelt ⟨"%40"⟩; Code.part23; dropfelt ⟨"%11"⟩; dropfelt ⟨"%42"⟩; dropfelt ⟨"%45"⟩; Code.part24; dropfelt ⟨"%13"⟩; dropfelt ⟨"%46"⟩; dropfelt ⟨"%47"⟩; dropfelt ⟨"%48"⟩; Code.part25; dropfelt ⟨"%43"⟩; dropfelt ⟨"%49"⟩; dropfelt ⟨"%44"⟩; dropfelt ⟨"%50"⟩; dropfelt ⟨"%51"⟩; Code.part26; dropfelt ⟨"%22"⟩; dropfelt ⟨"%52"⟩; dropfelt ⟨"%41"⟩; dropfelt ⟨"%53"⟩; dropfelt ⟨"%54"⟩; Code.part27; dropfelt ⟨"%7"⟩; dropfelt ⟨"%56"⟩; dropfelt ⟨"%59"⟩; Code.part28; dropfelt ⟨"%15"⟩; dropfelt ⟨"%60"⟩; dropfelt ⟨"%58"⟩; dropfelt ⟨"%61"⟩; dropfelt ⟨"%63"⟩; Code.part29; dropfelt ⟨"%57"⟩; dropfelt ⟨"%62"⟩; dropfelt ⟨"%64"⟩; dropfelt ⟨"%65"⟩; dropfelt ⟨"%66"⟩; dropfelt ⟨"%55"⟩; Code.part30; dropfelt ⟨"%19"⟩; dropfelt ⟨"%21"⟩; dropfelt ⟨"%67"⟩; dropfelt ⟨"%68"⟩; dropfelt ⟨"%70"⟩; Code.part31; dropfelt ⟨"%20"⟩; dropfelt ⟨"%71"⟩; dropfelt ⟨"%69"⟩; dropfelt ⟨"%72"⟩; dropfelt ⟨"%73"⟩⟧) := by
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
  rewrite [←Code.opt_full_def]
  unfold MLIR.runProgram
  rewrite [←Code.parts_combine]
  unfold Code.parts_combined
  rewrite [←Code.getReturn_ignores_drops]
  rw [←Code.behaviour_with_drops]

-- lemma closed_form {x₀ x₁ x₂ x₃: Felt} {y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ y₁₄ y₁₅ y₁₆ y₁₇ : Option Felt} :
--   Code.run (start_state [x₀, x₁, x₂, x₃]) = [y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂, y₁₃, y₁₄, y₁₅, y₁₆, y₁₇ ] ↔ sorry := by

lemma closed_form_part0 {x₀ x₁ x₂ x₃: Felt} {y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ y₁₄ y₁₅ y₁₆ y₁₇ : Option Felt} :
    Code.run (start_state [x₀, x₁, x₂, x₃]) = [y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂, y₁₃, y₁₄, y₁₅, y₁₆, y₁₇] ↔
    Code.getReturn
      (part1_state_update
        (((({
                  buffers :=
                    ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                        [[none, none, none, none, none, none, none, none, none, none, none, none, none, none, none,
                            none, none, none]])[{ name := "in" }] ←ₘ
                      [[some x₀, some x₁, some x₂, some x₃]],
                  bufferWidths := ((fun x => Map.empty x)[{ name := "data" }] ←ₘ 18)[{ name := "in" }] ←ₘ 4,
                  constraints := [], cycle := 0, felts := Map.empty, isFailed := false, props := Map.empty,
                  vars := [{ name := "in" }, { name := "data" }] }[felts][{ name := "%19" }] ←
                128)[felts][{ name := "%23" }] ←
              x₃)[felts][{ name := "%74" }] ←
            feltBitAnd x₃ 128)[felts][{ name := "%18" }] ←
          1997537281)) =
    [y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂, y₁₃, y₁₄, y₁₅, y₁₆, y₁₇] := by
    rewrite [use_opt_full]
    
    rewrite [part0_wp]
    rewrite [part1_updates_opaque]
    unfold start_state part0_state
    MLIR_states_updates
    unfold part0_drops
    -- no drops
    -- no sets
    rfl

lemma closed_form_part1 {x₀ x₁ x₂ x₃: Felt} {y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ y₁₄ y₁₅ y₁₆ y₁₇ : Option Felt} :
    Code.getReturn
      (part1_state_update
        (((({
                  buffers :=
                    ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                        [[none, none, none, none, none, none, none, none, none, none, none, none, none, none, none,
                            none, none, none]])[{ name := "in" }] ←ₘ
                      [[some x₀, some x₁, some x₂, some x₃]],
                  bufferWidths := ((fun x => Map.empty x)[{ name := "data" }] ←ₘ 18)[{ name := "in" }] ←ₘ 4,
                  constraints := [], cycle := 0, felts := Map.empty, isFailed := false, props := Map.empty,
                  vars := [{ name := "in" }, { name := "data" }] }[felts][{ name := "%19" }] ←
                128)[felts][{ name := "%23" }] ←
              x₃)[felts][{ name := "%74" }] ←
            feltBitAnd x₃ 128)[felts][{ name := "%18" }] ←
          1997537281)) =
    [y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂, y₁₃, y₁₄, y₁₅, y₁₆, y₁₇] ↔
    Code.getReturn
      (part2_state_update
        {
          buffers :=
            (Map.empty[{ name := "in" }] ←ₘ [[some x₀, some x₁, some x₂, some x₃]])[{ name := "data" }] ←ₘ
              [[none, none, none, none, none, none, none, none, none, none, some (feltBitAnd x₃ 128 * 1997537281), none,
                  none, none, none, none, none, none]],
          bufferWidths := ((fun x => Map.empty x)[{ name := "data" }] ←ₘ 18)[{ name := "in" }] ←ₘ 4, constraints := [],
          cycle := 0,
          felts :=
            ((((Map.empty[{ name := "%19" }] ←ₘ 128)[{ name := "%23" }] ←ₘ x₃)[{ name := "%18" }] ←ₘ
                  1997537281)[{ name := "%17" }] ←ₘ
                96)[{ name := "%76" }] ←ₘ
              feltBitAnd x₃ 96,
          isFailed := false, props := Map.empty, vars := [{ name := "in" }, { name := "data" }] }) =
    [y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂, y₁₃, y₁₄, y₁₅, y₁₆, y₁₇] := by
      rewrite [part2_updates_opaque]
      unfold part1_state
      MLIR_states_updates
      unfold part1_drops
      simp [State.dropFelts]
      MLIR_states_updates
      simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
      rewrite [Map.drop_of_updates]
      simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

    -- rewrite [part3_updates_opaque]
    -- unfold part2_state
    -- MLIR_states_updates
    -- unfold part2_drops
    -- simp [State.dropFelts]
    -- MLIR_states_updates
    -- simp only [ne_eq, Map.update_drop_swap, Map.update_drop, Map.drop_base]
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

    -- rewrite [part4_updates_opaque]
    -- unfold part3_state
    -- MLIR_states_updates
    -- unfold part3_drops
    -- simp [State.dropFelts]
    -- MLIR_states_updates
    -- simp only [ne_eq, Map.update_drop_swap, Map.update_drop, Map.drop_base]
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

    -- rewrite [part5_updates_opaque]
    -- unfold part4_state
    -- MLIR_states_updates
    -- unfold part4_drops
    -- simp [State.dropFelts]
    -- MLIR_states_updates
    -- simp only [ne_eq, Map.update_drop_swap, Map.update_drop, Map.drop_base]

    -- rewrite [part6_updates_opaque]
    -- unfold part5_state
    -- MLIR_states_updates
    -- unfold part5_drops
    -- simp [State.dropFelts]
    -- MLIR_states_updates
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

    -- rewrite [part7_updates_opaque]
    -- unfold part6_state
    -- MLIR_states_updates
    -- unfold part6_drops
    -- simp [State.dropFelts]
    -- MLIR_states_updates
    -- simp only [ne_eq, Map.update_drop_swap, Map.update_drop, Map.drop_base]
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

    -- rewrite [part8_updates_opaque]
    -- unfold part7_state
    -- MLIR_states_updates
    -- unfold part7_drops
    -- simp [State.dropFelts]
    -- MLIR_states_updates
    -- simp only [ne_eq, Map.update_drop_swap, Map.update_drop, Map.drop_base]
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

    -- rewrite [part9_updates_opaque]
    -- unfold part8_state
    -- MLIR_states_updates
    -- unfold part8_drops
    -- simp [State.dropFelts]
    -- MLIR_states_updates
    -- simp only [ne_eq, Map.update_drop_swap, Map.update_drop, Map.drop_base]
    -- rewrite [Map.drop_of_updates, Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

    -- rewrite [part10_updates_opaque]
    -- unfold part9_state
    -- MLIR_states_updates
    -- unfold part9_drops
    -- simp [State.dropFelts]
    -- MLIR_states_updates
    -- simp only [ne_eq, Map.update_drop_swap, Map.update_drop, Map.drop_base]
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

    -- rewrite [part11_updates_opaque]
    -- unfold part10_state
    -- MLIR_states_updates
    -- unfold part10_drops
    -- simp [State.dropFelts]
    -- MLIR_states_updates
    -- simp only [ne_eq, Map.update_drop_swap, Map.update_drop, Map.drop_base]
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

    -- rewrite [part12_updates_opaque]
    -- unfold part11_state
    -- MLIR_states_updates
    -- unfold part11_drops
    -- simp [State.dropFelts]
    -- MLIR_states_updates
    -- simp only [ne_eq, Map.update_drop_swap, Map.update_drop, Map.drop_base]
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

    -- rewrite [part13_updates_opaque]
    -- unfold part12_state
    -- MLIR_states_updates
    -- unfold part12_drops
    -- simp [State.dropFelts]
    -- MLIR_states_updates
    -- simp only [ne_eq, Map.update_drop_swap, Map.update_drop, Map.drop_base]
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

    -- rewrite [part14_updates_opaque]
    -- unfold part13_state
    -- MLIR_states_updates
    -- unfold part13_drops
    -- simp [State.dropFelts]
    -- MLIR_states_updates
    -- simp only [ne_eq, Map.update_drop_swap, Map.update_drop, Map.drop_base]
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

    -- rewrite [part15_updates_opaque]
    -- unfold part14_state
    -- MLIR_states_updates
    -- unfold part14_drops
    -- simp [State.dropFelts]
    -- MLIR_states_updates
    -- simp only [ne_eq, Map.update_drop_swap, Map.update_drop, Map.drop_base]
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

    -- rewrite [part16_updates_opaque]
    -- unfold part15_state
    -- MLIR_states_updates
    -- unfold part15_drops
    -- simp [State.dropFelts]
    -- MLIR_states_updates
    -- simp only [ne_eq, Map.update_drop_swap, Map.update_drop, Map.drop_base]
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

    -- rewrite [part17_updates_opaque]
    -- unfold part16_state
    -- MLIR_states_updates
    -- unfold part16_drops
    -- simp [State.dropFelts]
    -- MLIR_states_updates
    -- simp only [ne_eq, Map.update_drop_swap, Map.update_drop, Map.drop_base]
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]


-- def part17 : MLIRProgram :=   2
-- def part18 : MLIRProgram :=   0
-- def part19 : MLIRProgram :=   0
-- def part20 : MLIRProgram :=   0
-- def part21 : MLIRProgram :=   0
-- def part22 : MLIRProgram :=   0
-- def part23 : MLIRProgram :=   0
-- def part24 : MLIRProgram :=   0
-- def part25 : MLIRProgram :=   0
-- def part26 : MLIRProgram :=   0
-- def part27 : MLIRProgram :=   0
-- def part28 : MLIRProgram :=   0
-- def part29 : MLIRProgram :=   0
-- def part30 : MLIRProgram :=   0
-- def part31 : MLIRProgram :=   0
  

--   -- Code.run (start_state [x₀, x₁, x₂, x₃]) = [y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂, y₁₃, y₁₄, y₁₅, y₁₆, y₁₇ ] ↔ sorry := by
--   -- rewrite [part0_wp]
--   -- rewrite [part1_updates_opaque]
--   -- unfold start_state
--   -- unfold part0_state
--   -- MLIR_states_updates

--   -- rewrite [part2_updates_opaque]
--   -- unfold part1_state
--   -- MLIR_states_updates

--   -- rewrite [part3_updates_opaque]
--   -- unfold part2_state
--   -- MLIR_states_updates

--   -- rewrite [part4_updates_opaque]
--   -- unfold part3_state
--   -- MLIR_states_updates

--   -- rewrite [part5_updates_opaque]
--   -- unfold part4_state
--   -- MLIR_states_updates

--   -- rewrite [part6_updates_opaque]
--   -- unfold part5_state
--   -- MLIR_states_updates

--   -- rewrite [part7_updates_opaque]
--   -- unfold part6_state
--   -- MLIR_states_updates


--   -- generalize h_none : [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none] = nones

--   -- -- rewrite [part8_updates_opaque]
--   -- -- unfold part7_state
--   -- -- MLIR_witness_updates

--   -- -- rewrite [part9_updates_opaque]
--   -- -- unfold part8_state
--   -- -- MLIR_witness_updates

--   -- -- rewrite [part₃_updates_opaque]
--   -- -- rewrite [part₄_updates_opaque]
--   -- -- rewrite [part₅_updates_opaque]



--   -- -- unfold part₁_state
--   -- -- MLIR_witness_updates

--   -- -- unfold part₂_state
--   -- -- MLIR_witness_updates

--   -- -- unfold part₃_state
--   -- -- MLIR_witness_updates

--   -- -- unfold part₄_state
--   -- -- MLIR_witness_updates

--   -- -- unfold part₅_state
--   -- -- MLIR_witness_updates

--   -- -- simp [State.lastOutput, Option.get!, List.getLast!, List.getLast, State.buffers]
--   -- -- MLIR_witness_updates
--   -- -- simp [List.getLast]

end Risc0.ComputeDecode.Witness.WP
