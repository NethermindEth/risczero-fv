import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot2.Constraints.Code
import Risc0.Gadgets.OneHot2.Constraints.WeakestPresPart0

namespace Risc0.OneHot2.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part1 on st
def part1_state (st: State) : State :=
  
        ((((st[props][{ name := "%5" }] ←
                (Option.get! (State.props st { name := "%1" }) ∧
                  Option.get! (State.felts st { name := "%4" }) = 0))[felts][{ name := "%0" }] ←
              1)["%6"] ←ₛ
            getImpl st { name := "data" } 0 0)[felts][{ name := "%7" }] ←
          1 -
            Option.get!
              (State.felts
                (((st[props][{ name := "%5" }] ←
                      (Option.get! (State.props st { name := "%1" }) ∧
                        Option.get! (State.felts st { name := "%4" }) = 0))[felts][{ name := "%0" }] ←
                    1)["%6"] ←ₛ
                  getImpl st { name := "data" } 0 0)
                { name := "%6" })) 

def part1_drops (st: State) : State :=
  State.dropFelts (st) ⟨"%4"⟩

-- Run the program from part1 onwards by using part1_state rather than Code.part1
def part1_state_update (st: State): State :=
  Γ (part1_drops (part1_state st)) ⟦Code.part2;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%10"⟩;Code.part3;dropfelt ⟨"%1"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%15"⟩⟧

-- Prove that substituting part1_state for Code.part1 produces the same result
lemma part1_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part1;dropfelt ⟨"%4"⟩;Code.part2;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%10"⟩;Code.part3;dropfelt ⟨"%1"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%15"⟩) st) ↔
  Code.getReturn (part1_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%4"⟩;Code.part2;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%10"⟩;Code.part3;dropfelt ⟨"%1"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%15"⟩) = prog
  unfold Code.part1
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part1_state_update part1_drops part1_state
  rfl

lemma part1_updates_opaque {st : State} : 
  Code.getReturn (part0_state_update st) ↔
  Code.getReturn (part1_state_update (part0_drops (part0_state st))) := by
  simp [part0_state_update, part1_wp]

lemma part1_cumulative_wp {x0 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19: Felt} :
  Code.run (start_state [x0] ([y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19])) ↔
  Code.getReturn
      (part1_state_update
        ((({
                buffers :=
                  ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                      [[some y0, some y1, some y2, some y3, some y4, some y5, some y6, some y7, some y8, some y9,
                          some y10, some y11, some y12, some y13, some y14, some y15, some y16, some y17, some y18,
                          some y19]])[{ name := "code" }] ←ₘ
                    [[some x0]],
                bufferWidths := ((fun x => Map.empty x)[{ name := "data" }] ←ₘ 20)[{ name := "code" }] ←ₘ 1,
                constraints := [], cycle := 0, felts := Map.empty, isFailed := false, props := Map.empty,
                vars := [{ name := "code" }, { name := "data" }] }[props][{ name := "%1" }] ←
              True)[felts][{ name := "%3" }] ←
            y1)[felts][{ name := "%4" }] ←
          y1 - x0))  := by
    rewrite [part0_cumulative_wp]
    rewrite [part1_updates_opaque]
    unfold part0_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part0_drops
    -- 1 drop
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

end Risc0.OneHot2.Constraints.WP