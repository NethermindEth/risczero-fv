import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot2.Witness.Code
import Risc0.Gadgets.OneHot2.Witness.WeakestPresPart1

namespace Risc0.OneHot2.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part2 on st
def part2_state (st: State) : State :=
  sorry

def part2_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (st) ⟨"%2"⟩) ⟨"%4"⟩

-- Run the program from part2 onwards by using part2_state rather than Code.part2
def part2_state_update (st: State): State :=
  Γ (part2_drops (part2_state st)) ⟦Code.part3;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;Code.part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;Code.part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧

-- Prove that substituting part2_state for Code.part2 produces the same result
lemma part2_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;Code.part3;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;Code.part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;Code.part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part2_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;Code.part3;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;Code.part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;Code.part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩) = prog
  unfold Code.part2
  MLIR

lemma part2_updates_opaque {st : State} : 
  Code.getReturn (part1_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part2_state_update (part1_drops (part1_state st))) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part1_state_update, part2_wp]

lemma part2_cumulative_wp {x0: Felt} :
  Code.run (start_state [x0]) = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19] ↔
  sorry := by
    rewrite [part1_cumulative_wp]
    rewrite [part2_updates_opaque]
    unfold part1_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part1_drops
    -- 2 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 1 set
    rewrite [Map.drop_of_updates]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    rfl

end Risc0.OneHot2.Witness.WP