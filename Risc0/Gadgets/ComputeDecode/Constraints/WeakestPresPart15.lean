import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart14

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part15 on st
def part15_state (st: State) : State :=
  
        ((((st["%59"] ←ₛ getImpl st { name := "data" } 0 17)[felts][{ name := "%62" }] ←
              Option.get! (State.felts st { name := "%61" }) +
                Option.get! (State.felts (st["%59"] ←ₛ getImpl st { name := "data" } 0 17) { name := "%59" }))["%7"] ←ₛ
            getImpl st { name := "in" } 0 0)[felts][{ name := "%63" }] ←
          Option.get!
              (State.felts
                (((st["%59"] ←ₛ getImpl st { name := "data" } 0 17)[felts][{ name := "%62" }] ←
                    Option.get! (State.felts st { name := "%61" }) +
                      Option.get!
                        (State.felts (st["%59"] ←ₛ getImpl st { name := "data" } 0 17) { name := "%59" }))["%7"] ←ₛ
                  getImpl st { name := "in" } 0 0)
                { name := "%7" }) -
            (Option.get! (State.felts st { name := "%61" }) +
              Option.get! (State.felts (st["%59"] ←ₛ getImpl st { name := "data" } 0 17) { name := "%59" }))) 

def part15_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%61"⟩) ⟨"%59"⟩) ⟨"%62"⟩) ⟨"%7"⟩

-- Run the program from part15 onwards by using part15_state rather than Code.part15
def part15_state_update (st: State): State :=
  Γ (part15_drops (part15_state st)) ⟦Code.part16;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩⟧

-- Prove that substituting part15_state for Code.part15 produces the same result
lemma part15_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩) st) ↔
  Code.getReturn (part15_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩) = prog
  unfold Code.part15
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part15_state_update part15_drops part15_state
  rfl

lemma part15_updates_opaque {st : State} : 
  Code.getReturn (part14_state_update st) ↔
  Code.getReturn (part15_state_update (part14_drops (part14_state st))) := by
  simp [part14_state_update, part15_wp]

lemma part15_cumulative_wp {x0 x1 x2 x3 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17: Felt} :
  Code.run (start_state [x0,x1,x2,x3] ([y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17])) ↔
  Code.getReturn
      (part15_state_update
        ((((({
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
                x2 - ((y12 * 8 + y2 * 2 + y11) * 16 + y4 * 4 + y3) = 0))[props][{ name := "%58" }] ←
            ((x3 - ((y10 * 64 + (y1 * 16 + y9 * 8 + y8 * 4 + y0)) * 2 + y13) = 0 ∧
                x2 - ((y12 * 8 + y2 * 2 + y11) * 16 + y4 * 4 + y3) = 0) ∧
              x1 - (y14 * 128 + (y15 * 4 + y5) * 16 + y7 * 4 + y6) = 0))[felts][{ name := "%61" }] ←
          y16 * 128))  := by
    rewrite [part14_cumulative_wp]
    rewrite [part15_updates_opaque]
    unfold part14_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part14_drops
    -- 5 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

end Risc0.ComputeDecode.Constraints.WP