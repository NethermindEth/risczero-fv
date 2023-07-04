import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot1.Witness.Code
import Risc0.Gadgets.OneHot1.Witness.WeakestPresPart1

namespace Risc0.OneHot1.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part2 on st
def part2_state (st: State) : State :=
  
          ((withEqZero
              (Option.get! (State.felts st { name := "%4" }) *
                (Option.get! (State.felts st { name := "%0" }) - Option.get! (State.felts st { name := "%4" })))
              ((st[felts][{ name := "%5" }] ←
                  Option.get! (State.felts st { name := "%0" }) -
                    Option.get! (State.felts st { name := "%4" }))[felts][{ name := "%6" }] ←
                Option.get! (State.felts st { name := "%4" }) *
                  (Option.get! (State.felts st { name := "%0" }) -
                    Option.get! (State.felts st { name := "%4" }))))[felts][{ name := "%7" }] ←
            Option.get! (State.felts st { name := "%4" }) - Option.get! (State.felts st { name := "%0" })) 

def part2_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%0"⟩) ⟨"%4"⟩) ⟨"%5"⟩) ⟨"%6"⟩

-- Run the program from part2 onwards by using part2_state rather than Code.part2
def part2_state_update (st: State): State :=
  Γ (part2_drops (part2_state st)) ⟦Code.part3;dropfelt ⟨"%7"⟩⟧

-- Prove that substituting part2_state for Code.part2 produces the same result
lemma part2_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part2;dropfelt ⟨"%0"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%6"⟩;Code.part3;dropfelt ⟨"%7"⟩) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part2_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%0"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%6"⟩;Code.part3;dropfelt ⟨"%7"⟩) = prog
  unfold Code.part2
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part2_state_update part2_drops part2_state
  rfl

lemma part2_updates_opaque {st : State} : 
  Code.getReturn (part1_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part2_state_update (part1_drops (part1_state st))) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part1_state_update, part2_wp]

lemma part2_cumulative_wp {x0: Felt} :
  Code.run (start_state [x0]) = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19] ↔
  Code.getReturn
        (part2_state_update
          (({
                buffers :=
                  ((fun x => Map.empty x)[{ name := "code" }] ←ₘ [[some x0]])[{ name := "data" }] ←ₘ
                    [[some (if x0 = 0 then 1 else 0), none, none, none, none, none, none, none, none, none, none, none,
                        none, none, none, none, none, none, none, none]],
                bufferWidths := ((fun x => Map.empty x)[{ name := "data" }] ←ₘ 20)[{ name := "code" }] ←ₘ 1,
                constraints := [x0 = 0], cycle := 0, felts := Map.empty, isFailed := false, props := Map.empty,
                vars := [{ name := "code" }, { name := "data" }] }[felts][{ name := "%0" }] ←
              1)[felts][{ name := "%4" }] ←
            if x0 = 0 then 1 else 0)) =
      [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19]  := by
    rewrite [part1_cumulative_wp]
    rewrite [part2_updates_opaque]
    unfold part1_state
    MLIR_states_updates
    -- 1 withEqZero
    rewrite [withEqZero_def]
    MLIR_states_updates
    unfold part1_drops
    -- 3 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

end Risc0.OneHot1.Witness.WP