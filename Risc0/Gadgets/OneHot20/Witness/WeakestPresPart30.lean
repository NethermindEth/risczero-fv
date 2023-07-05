import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart29

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part30 on st
def part30_state (st: State) : State :=
  
          (((withEqZero
                (Option.get! (State.felts st { name := "%21" }) - Option.get! (State.felts st { name := "%67" }))
                (st[felts][{ name := "%68" }] ←
                  Option.get! (State.felts st { name := "%21" }) -
                    Option.get! (State.felts st { name := "%67" })))["%70"] ←ₛ
              getImpl st { name := "data" } 0 16)[felts][{ name := "%71" }] ←
            Option.get!
                (State.felts
                  ((withEqZero
                      (Option.get! (State.felts st { name := "%21" }) - Option.get! (State.felts st { name := "%67" }))
                      (st[felts][{ name := "%68" }] ←
                        Option.get! (State.felts st { name := "%21" }) -
                          Option.get! (State.felts st { name := "%67" })))["%70"] ←ₛ
                    getImpl st { name := "data" } 0 16)
                  { name := "%70" }) *
              Option.get! (State.felts st { name := "%19" })) 

def part30_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%19"⟩) ⟨"%21"⟩) ⟨"%67"⟩) ⟨"%68"⟩) ⟨"%70"⟩

-- Run the program from part30 onwards by using part30_state rather than Code.part30
def part30_state_update (st: State): State :=
  Γ (part30_drops (part30_state st)) ⟦Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩⟧

-- Prove that substituting part30_state for Code.part30 produces the same result
lemma part30_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part30_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) = prog
  unfold Code.part30
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part30_state_update part30_drops part30_state
  rfl

lemma part30_updates_opaque {st : State} : 
  Code.getReturn (part29_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part30_state_update (part29_drops (part29_state st))) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part29_state_update, part30_wp]

lemma part30_cumulative_wp {x0 x1 x2 x3: Felt} :
  Code.run (start_state [x0,x1,x2,x3]) = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17] ↔
  Code.getReturn
        (part30_state_update
          ({
              buffers :=
                ((fun x => Map.empty x)[{ name := "in" }] ←ₘ
                    [[some x0, some x1, some x2, some x3]])[{ name := "data" }] ←ₘ
                  [[some (feltBitAnd x3 6 * 1006632961), some (feltBitAnd x3 96 * 1950351361),
                      some (feltBitAnd x2 96 * 1950351361), some (feltBitAnd x2 3),
                      some (feltBitAnd x2 12 * 1509949441), some (feltBitAnd x1 48 * 1887436801),
                      some (feltBitAnd x1 3), some (feltBitAnd x1 12 * 1509949441), some (feltBitAnd x3 8 * 1761607681),
                      some (feltBitAnd x3 16 * 1887436801), some (feltBitAnd x3 128 * 1997537281),
                      some (feltBitAnd x2 16 * 1887436801), some (feltBitAnd x2 128 * 1997537281),
                      some (feltBitAnd x3 1), some (feltBitAnd x1 128 * 1997537281),
                      some (feltBitAnd x1 64 * 1981808641), some (feltBitAnd x0 128 * 1997537281),
                      some (feltBitAnd x0 127)]],
              bufferWidths := ((fun x => Map.empty x)[{ name := "data" }] ←ₘ 18)[{ name := "in" }] ←ₘ 4,
              constraints :=
                [x2 -
                      ((feltBitAnd x2 128 * 1997537281 * 8 + feltBitAnd x2 96 * 1950351361 * 2 +
                              feltBitAnd x2 16 * 1887436801) *
                            16 +
                          feltBitAnd x2 12 * 1509949441 * 4 +
                        feltBitAnd x2 3) =
                    0,
                  x3 -
                      ((feltBitAnd x3 128 * 1997537281 * 64 +
                            (feltBitAnd x3 96 * 1950351361 * 16 + feltBitAnd x3 16 * 1887436801 * 8 +
                                feltBitAnd x3 8 * 1761607681 * 4 +
                              feltBitAnd x3 6 * 1006632961)) *
                          2 +
                        feltBitAnd x3 1) =
                    0],
              cycle := 0,
              felts := ((Map.empty[{ name := "%19" }] ←ₘ 128)[{ name := "%21" }] ←ₘ x1)[{ name := "%20" }] ←ₘ x0,
              isFailed := false, props := Map.empty,
              vars := [{ name := "in" }, { name := "data" }] }[felts][{ name := "%67" }] ←
            feltBitAnd x1 128 * 1997537281 * 128 +
                  (feltBitAnd x1 64 * 1981808641 * 4 + feltBitAnd x1 48 * 1887436801) * 16 +
                feltBitAnd x1 12 * 1509949441 * 4 +
              feltBitAnd x1 3)) =
      [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17]  := by
    rewrite [part29_cumulative_wp]
    rewrite [part30_updates_opaque]
    unfold part29_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part29_drops
    -- 6 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

end Risc0.OneHot20.Witness.WP