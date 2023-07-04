import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot1.Constraints.Code
import Risc0.Gadgets.OneHot1.Constraints.WeakestPresPart1

namespace Risc0.OneHot1.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part2 on st
def part2_state (st: State) : State :=
  
        ((((st[felts][{ name := "%8" }] ←
                Option.get! (State.felts st { name := "%6" }) *
                  Option.get! (State.felts st { name := "%7" }))[props][{ name := "%9" }] ←
              (Option.get! (State.props st { name := "%5" }) ∧
                (Option.get! (State.felts st { name := "%6" }) = 0 ∨
                  Option.get! (State.felts st { name := "%7" }) = 0)))[felts][{ name := "%10" }] ←
            Option.get! (State.felts st { name := "%6" }) -
              Option.get! (State.felts st { name := "%1" }))[props][{ name := "%11" }] ←
          ((Option.get! (State.props st { name := "%5" }) ∧
              (Option.get! (State.felts st { name := "%6" }) = 0 ∨ Option.get! (State.felts st { name := "%7" }) = 0)) ∧
            Option.get! (State.felts st { name := "%6" }) - Option.get! (State.felts st { name := "%1" }) =
              0)) 

def part2_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%2"⟩) ⟨"%5"⟩) ⟨"%1"⟩) ⟨"%6"⟩) ⟨"%7"⟩) ⟨"%8"⟩) ⟨"%9"⟩) ⟨"%10"⟩) ⟨"%11"⟩

-- Run the program from part2 onwards by using part2_state rather than Code.part2
def part2_state_update (st: State): State :=
  part2_drops (part2_state st)

-- Prove that substituting part2_state for Code.part2 produces the same result
lemma part2_wp {st : State}:
  Code.getReturn (MLIR.runProgram (Code.part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%11"⟩) st) ↔
  Code.getReturn (part2_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%2"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%11"⟩) = prog
  unfold Code.part2
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_dropfelt]
  unfold part2_state_update part2_drops part2_state
  rfl

lemma part2_updates_opaque {st : State} : 
  Code.getReturn (part1_state_update st) ↔
  Code.getReturn (part2_state_update (part1_drops (part1_state st))) := by
  simp [part1_state_update, part2_wp]

lemma part2_cumulative_wp {x0 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19: Felt} :
  Code.run (start_state [x0] ([y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19])) ↔
  Code.getReturn
      (part2_state_update
        ((((({
                    buffers :=
                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                          [[some y0, some y1, some y2, some y3, some y4, some y5, some y6, some y7, some y8, some y9,
                              some y10, some y11, some y12, some y13, some y14, some y15, some y16, some y17, some y18,
                              some y19]])[{ name := "code" }] ←ₘ
                        [[some x0]],
                    bufferWidths := ((fun x => Map.empty x)[{ name := "data" }] ←ₘ 20)[{ name := "code" }] ←ₘ 1,
                    constraints := [], cycle := 0, felts := Map.empty, isFailed := false, props := Map.empty,
                    vars := [{ name := "code" }, { name := "data" }] }[props][{ name := "%2" }] ←
                  True)[props][{ name := "%5" }] ←
                x0 = 0)[felts][{ name := "%1" }] ←
              1)[felts][{ name := "%6" }] ←
            y0)[felts][{ name := "%7" }] ←
          1 - y0))  := by
    rewrite [part1_cumulative_wp]
    rewrite [part2_updates_opaque]
    unfold part1_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part1_drops
    -- 1 drop
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

lemma closed_form {x0 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19: Felt} :
  Code.run (start_state [x0] ([y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19])) ↔
   (x0 = 0 ∧ (y0 = 0 ∨ 1 - y0 = 0)) ∧ y0 - 1 = 0  := by
    rewrite [part2_cumulative_wp]
    unfold part2_state_update
    unfold part2_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part2_drops
    -- 9 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    unfold Code.getReturn
    simp only
    simp only [Code.getReturn, State.constraintsInVar, State.updateProps_props_get_wobbly, Option.getD_some]
end Risc0.OneHot1.Constraints.WP