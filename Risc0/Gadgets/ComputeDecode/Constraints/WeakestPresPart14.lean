import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart13

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part14 on st
def part14_state (st: State) : State :=
  
        ((((st[felts][{ name := "%57" }] ←
                Option.get! (State.felts st { name := "%8" }) -
                  Option.get! (State.felts st { name := "%56" }))[props][{ name := "%58" }] ←
              (Option.get! (State.props st { name := "%43" }) ∧
                Option.get! (State.felts st { name := "%8" }) - Option.get! (State.felts st { name := "%56" }) =
                  0))["%60"] ←ₛ
            getImpl st { name := "data" } 0 16)[felts][{ name := "%61" }] ←
          Option.get!
              (State.felts
                (((st[felts][{ name := "%57" }] ←
                      Option.get! (State.felts st { name := "%8" }) -
                        Option.get! (State.felts st { name := "%56" }))[props][{ name := "%58" }] ←
                    (Option.get! (State.props st { name := "%43" }) ∧
                      Option.get! (State.felts st { name := "%8" }) - Option.get! (State.felts st { name := "%56" }) =
                        0))["%60"] ←ₛ
                  getImpl st { name := "data" } 0 16)
                { name := "%60" }) *
            Option.get! (State.felts st { name := "%0" })) 

def part14_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%0"⟩) ⟨"%56"⟩) ⟨"%8"⟩) ⟨"%57"⟩) ⟨"%60"⟩

-- Run the program from part14 onwards by using part14_state rather than Code.part14
def part14_state_update (st: State): State :=
  Γ (part14_drops (part14_state st)) ⟦Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩⟧

-- Prove that substituting part14_state for Code.part14 produces the same result
lemma part14_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩) st) ↔
  Code.getReturn (part14_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩) = prog
  unfold Code.part14
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part14_state_update part14_drops part14_state
  rfl

lemma part14_updates_opaque {st : State} : 
  Code.getReturn (part13_state_update st) ↔
  Code.getReturn (part14_state_update (part13_drops (part13_state st))) := by
  simp [part13_state_update, part14_wp]

lemma part14_cumulative_wp {x0 x1 x2 x3 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17: Felt} :
  Code.run (start_state [x0,x1,x2,x3] ([y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17])) ↔
  Code.getReturn
      (part14_state_update
        (((((({
                      buffers :=
                        ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                            [[some y0, some y1, some y2, some y3, some y4, some y5, some y6, some y7, some y8, some y9,
                                some y10, some y11, some y12, some y13, some y14, some y15, some y16,
                                some y17]])[{ name := "in" }] ←ₘ
                          [[some x0, some x1, some x2, some x3]],
                      bufferWidths := ((fun x => Map.empty x)[{ name := "data" }] ←ₘ 18)[{ name := "in" }] ←ₘ 4,
                      constraints := [], cycle := 0, felts := Map.empty, isFailed := false, props := Map.empty,
                      vars := [{ name := "in" }, { name := "data" }] }[props][{ name := "%6" }] ←
                    True)[props][{ name := "%28" }] ←
                  x3 - ((y10 * 64 + (y1 * 16 + y9 * 8 + y8 * 4 + y0)) * 2 + y13) = 0)[props][{ name := "%43" }] ←
                (x3 - ((y10 * 64 + (y1 * 16 + y9 * 8 + y8 * 4 + y0)) * 2 + y13) = 0 ∧
                  x2 - ((y12 * 8 + y2 * 2 + y11) * 16 + y4 * 4 + y3) = 0))[felts][{ name := "%0" }] ←
              128)[felts][{ name := "%56" }] ←
            y14 * 128 + (y15 * 4 + y5) * 16 + y7 * 4 + y6)[felts][{ name := "%8" }] ←
          x1))  := by
    rewrite [part13_cumulative_wp]
    rewrite [part14_updates_opaque]
    unfold part13_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part13_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

end Risc0.ComputeDecode.Constraints.WP