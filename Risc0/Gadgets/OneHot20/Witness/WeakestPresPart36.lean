import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart35

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part36 on st
def part36_state (st: State) : State :=
  sorry

def part36_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%22"⟩) ⟨"%82"⟩) ⟨"%83"⟩) ⟨"%84"⟩

-- Run the program from part36 onwards by using part36_state rather than Code.part36
def part36_state_update (st: State): State :=
  Γ (part36_drops (part36_state st)) ⟦Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩⟧

-- Prove that substituting part36_state for Code.part36 produces the same result
lemma part36_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part36_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) = prog
  unfold Code.part36
  MLIR

lemma part36_updates_opaque {st : State} : 
  Code.getReturn (part35_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part36_state_update (part35_drops (part35_state st))) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part35_state_update, part36_wp]

lemma part36_cumulative_wp {x0: Felt} :
  Code.run (start_state [x0]) = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19] ↔
  sorry := by
    rewrite [part35_cumulative_wp]
    rewrite [part36_updates_opaque]
    unfold part35_state
    try simplify_get_hack
    MLIR_states_updates
    -- 1 withEqZero
    rewrite [withEqZero_def]
    MLIR_states_updates
    unfold part35_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    rfl

end Risc0.OneHot20.Witness.WP