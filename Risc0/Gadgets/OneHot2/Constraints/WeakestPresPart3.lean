import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot2.Constraints.Code
import Risc0.Gadgets.OneHot2.Constraints.WeakestPresPart2

namespace Risc0.OneHot2.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part3 on st
def part3_state (st: State) : State :=
  
        ((((st[props][{ name := "%12" }] ←
                (Option.get! (State.props st { name := "%9" }) ∧
                  Option.get! (State.felts st { name := "%11" }) = 0))[felts][{ name := "%13" }] ←
              Option.get! (State.felts st { name := "%6" }) +
                Option.get! (State.felts st { name := "%3" }))[felts][{ name := "%14" }] ←
            Option.get! (State.felts st { name := "%6" }) + Option.get! (State.felts st { name := "%3" }) -
              Option.get! (State.felts st { name := "%0" }))[props][{ name := "%15" }] ←
          ((Option.get! (State.props st { name := "%9" }) ∧ Option.get! (State.felts st { name := "%11" }) = 0) ∧
            Option.get! (State.felts st { name := "%6" }) + Option.get! (State.felts st { name := "%3" }) -
                Option.get! (State.felts st { name := "%0" }) =
              0)) 

def part3_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%1"⟩) ⟨"%3"⟩) ⟨"%5"⟩) ⟨"%0"⟩) ⟨"%6"⟩) ⟨"%9"⟩) ⟨"%11"⟩) ⟨"%12"⟩) ⟨"%13"⟩) ⟨"%14"⟩) ⟨"%15"⟩

-- Run the program from part3 onwards by using part3_state rather than Code.part3
def part3_state_update (st: State): State :=
  part3_drops (part3_state st)

-- Prove that substituting part3_state for Code.part3 produces the same result
lemma part3_wp {st : State}:
  Code.getReturn (MLIR.runProgram (Code.part3;dropfelt ⟨"%1"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%15"⟩) st) ↔
  Code.getReturn (part3_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%1"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%15"⟩) = prog
  unfold Code.part3
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_dropfelt]
  unfold part3_state_update part3_drops part3_state
  rfl

lemma part3_updates_opaque {st : State} : 
  Code.getReturn (part2_state_update st) ↔
  Code.getReturn (part3_state_update (part2_drops (part2_state st))) := by
  simp [part2_state_update, part3_wp]

lemma part3_cumulative_wp {x0 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19: Felt} :
  Code.run (start_state [x0] ([y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19])) ↔
  Code.getReturn
      (part3_state_update
        ((((((({
                        buffers :=
                          ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                              [[some y0, some y1, some y2, some y3, some y4, some y5, some y6, some y7, some y8,
                                  some y9, some y10, some y11, some y12, some y13, some y14, some y15, some y16,
                                  some y17, some y18, some y19]])[{ name := "code" }] ←ₘ
                            [[some x0]],
                        bufferWidths := ((fun x => Map.empty x)[{ name := "data" }] ←ₘ 20)[{ name := "code" }] ←ₘ 1,
                        constraints := [], cycle := 0, felts := Map.empty, isFailed := false, props := Map.empty,
                        vars := [{ name := "code" }, { name := "data" }] }[props][{ name := "%1" }] ←
                      True)[felts][{ name := "%3" }] ←
                    y1)[props][{ name := "%5" }] ←
                  y1 - x0 = 0)[felts][{ name := "%0" }] ←
                1)[felts][{ name := "%6" }] ←
              y0)[props][{ name := "%9" }] ←
            (y1 - x0 = 0 ∧ (y0 = 0 ∨ 1 - y0 = 0)))[felts][{ name := "%11" }] ←
          y1 * (1 - y1)))  := by
    rewrite [part2_cumulative_wp]
    rewrite [part3_updates_opaque]
    unfold part2_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part2_drops
    -- 3 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

lemma closed_form {x0 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19: Felt} :
  Code.run (start_state [x0] ([y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19])) ↔
   ((y1 - x0 = 0 ∧ (y0 = 0 ∨ 1 - y0 = 0)) ∧ (y1 = 0 ∨ 1 - y1 = 0)) ∧ y0 + y1 - 1 = 0  := by
    rewrite [part3_cumulative_wp]
    unfold part3_state_update
    unfold part3_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part3_drops
    -- 11 drops
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
end Risc0.OneHot2.Constraints.WP