import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart15

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part16 on st
def part16_state (st: State) : State :=
  
        (st[props][{ name := "%64" }] ←
          (Option.get! (State.props st { name := "%58" }) ∧
            Option.get! (State.felts st { name := "%63" }) = (0 : Felt))) 

def part16_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%6"⟩) ⟨"%28"⟩) ⟨"%43"⟩) ⟨"%58"⟩) ⟨"%63"⟩) ⟨"%64"⟩

-- Run the program from part16 onwards by using part16_state rather than Code.part16
def part16_state_update (st: State): State :=
  part16_drops (part16_state st)

-- Prove that substituting part16_state for Code.part16 produces the same result
lemma part16_wp {st : State}:
  Code.getReturn (MLIR.runProgram (Code.part16;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩) st) ↔
  Code.getReturn (part16_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩) = prog
  unfold Code.part16
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_dropfelt]
  unfold part16_state_update part16_drops part16_state
  rfl

lemma part16_updates_opaque {st : State} : 
  Code.getReturn (part15_state_update st) ↔
  Code.getReturn (part16_state_update (part15_drops (part15_state st))) := by
  simp [part15_state_update, part16_wp]

lemma part16_cumulative_wp {x0 x1 x2 x3 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17: Felt} :
  Code.run (start_state [x0,x1,x2,x3] ([y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17])) ↔
  Code.getReturn
      (part16_state_update
        ((((({
                    buffers :=
                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                          [[some y0, some y1, some y2, some y3, some y4, some y5, some y6, some y7, some y8, some y9,
                              some y10, some y11, some y12, some y13, some y14, some y15, some y16,
                              some y17]])[{ name := "in" }] ←ₘ
                        [[some x0, some x1, some x2, some x3]],
                    bufferWidths :=
                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ (18 : ℕ))[{ name := "in" }] ←ₘ (4 : ℕ),
                    constraints := [], cycle := (0 : ℕ), felts := Map.empty, isFailed := false, props := Map.empty,
                    vars := [{ name := "in" }, { name := "data" }] }[props][{ name := "%6" }] ←
                  True)[props][{ name := "%28" }] ←
                x3 -
                    ((y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) * (2 : Felt) +
                      y13) =
                  (0 : Felt))[props][{ name := "%43" }] ←
              (x3 -
                    ((y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) * (2 : Felt) +
                      y13) =
                  (0 : Felt) ∧
                x2 - ((y12 * (8 : Felt) + y2 * (2 : Felt) + y11) * (16 : Felt) + y4 * (4 : Felt) + y3) =
                  (0 : Felt)))[props][{ name := "%58" }] ←
            ((x3 -
                    ((y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) * (2 : Felt) +
                      y13) =
                  (0 : Felt) ∧
                x2 - ((y12 * (8 : Felt) + y2 * (2 : Felt) + y11) * (16 : Felt) + y4 * (4 : Felt) + y3) = (0 : Felt)) ∧
              x1 - (y14 * (128 : Felt) + (y15 * (4 : Felt) + y5) * (16 : Felt) + y7 * (4 : Felt) + y6) =
                (0 : Felt)))[felts][{ name := "%63" }] ←
          x0 - (y16 * (128 : Felt) + y17)))  := by
    rewrite [part15_cumulative_wp]
    rewrite [part16_updates_opaque]
    unfold part15_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part15_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

lemma closed_form {x0 x1 x2 x3 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17: Felt} :
  Code.run (start_state [x0,x1,x2,x3] ([y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17])) ↔
   ((x3 - ((y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) * (2 : Felt) + y13) =
            (0 : Felt) ∧
          x2 - ((y12 * (8 : Felt) + y2 * (2 : Felt) + y11) * (16 : Felt) + y4 * (4 : Felt) + y3) = (0 : Felt)) ∧
        x1 - (y14 * (128 : Felt) + (y15 * (4 : Felt) + y5) * (16 : Felt) + y7 * (4 : Felt) + y6) = (0 : Felt)) ∧
      x0 - (y16 * (128 : Felt) + y17) = (0 : Felt)  := by
    rewrite [part16_cumulative_wp]
    unfold part16_state_update
    unfold part16_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part16_drops
    -- 6 drops
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
end Risc0.ComputeDecode.Constraints.WP