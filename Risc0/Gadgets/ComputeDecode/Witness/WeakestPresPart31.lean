import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart30

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part31 on st
def part31_state (st: State) : State :=
  
          (withEqZero
            (Option.get! (State.felts st { name := "%20" }) -
              (Option.get! (State.felts st { name := "%71" }) +
                Option.get! (State.felts (st["%69"] ←ₛ getImpl st { name := "data" } 0 17) { name := "%69" })))
            (((st["%69"] ←ₛ getImpl st { name := "data" } 0 17)[felts][{ name := "%72" }] ←
                Option.get! (State.felts st { name := "%71" }) +
                  Option.get!
                    (State.felts (st["%69"] ←ₛ getImpl st { name := "data" } 0 17)
                      { name := "%69" }))[felts][{ name := "%73" }] ←
              Option.get! (State.felts st { name := "%20" }) -
                (Option.get! (State.felts st { name := "%71" }) +
                  Option.get!
                    (State.felts (st["%69"] ←ₛ getImpl st { name := "data" } 0 17) { name := "%69" })))) 

def part31_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%20"⟩) ⟨"%71"⟩) ⟨"%69"⟩) ⟨"%72"⟩) ⟨"%73"⟩

-- Run the program from part31 onwards by using part31_state rather than Code.part31
def part31_state_update (st: State): State :=
  part31_drops (part31_state st)

-- Prove that substituting part31_state for Code.part31 produces the same result
lemma part31_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part31_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) = prog
  unfold Code.part31
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_dropfelt]
  unfold part31_state_update part31_drops part31_state
  rfl

lemma part31_updates_opaque {st : State} : 
  Code.getReturn (part30_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part31_state_update (part30_drops (part30_state st))) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part30_state_update, part31_wp]

lemma part31_cumulative_wp {x0 x1 x2 x3: Felt} :
  Code.run (start_state [x0,x1,x2,x3]) = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17] ↔
  Code.getReturn
        (part31_state_update
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
                [x1 -
                      (feltBitAnd x1 128 * 1997537281 * 128 +
                            (feltBitAnd x1 64 * 1981808641 * 4 + feltBitAnd x1 48 * 1887436801) * 16 +
                          feltBitAnd x1 12 * 1509949441 * 4 +
                        feltBitAnd x1 3) =
                    0,
                  x2 -
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
              cycle := 0, felts := Map.empty[{ name := "%20" }] ←ₘ x0, isFailed := false, props := Map.empty,
              vars := [{ name := "in" }, { name := "data" }] }[felts][{ name := "%71" }] ←
            feltBitAnd x0 128 * 1997537281 * 128)) =
      [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17]  := by
    rewrite [part30_cumulative_wp]
    rewrite [part31_updates_opaque]
    unfold part30_state
    MLIR_states_updates'
    -- 1 withEqZero
    rewrite [withEqZero_def]
    MLIR_states_updates'
    unfold part30_drops
    -- 5 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

lemma closed_form {x0 x1 x2 x3: Felt} :
  Code.run (start_state [x0,x1,x2,x3]) = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17] ↔
   some (feltBitAnd x3 6 * 1006632961) = y0 ∧
      some (feltBitAnd x3 96 * 1950351361) = y1 ∧
        some (feltBitAnd x2 96 * 1950351361) = y2 ∧
          some (feltBitAnd x2 3) = y3 ∧
            some (feltBitAnd x2 12 * 1509949441) = y4 ∧
              some (feltBitAnd x1 48 * 1887436801) = y5 ∧
                some (feltBitAnd x1 3) = y6 ∧
                  some (feltBitAnd x1 12 * 1509949441) = y7 ∧
                    some (feltBitAnd x3 8 * 1761607681) = y8 ∧
                      some (feltBitAnd x3 16 * 1887436801) = y9 ∧
                        some (feltBitAnd x3 128 * 1997537281) = y10 ∧
                          some (feltBitAnd x2 16 * 1887436801) = y11 ∧
                            some (feltBitAnd x2 128 * 1997537281) = y12 ∧
                              some (feltBitAnd x3 1) = y13 ∧
                                some (feltBitAnd x1 128 * 1997537281) = y14 ∧
                                  some (feltBitAnd x1 64 * 1981808641) = y15 ∧
                                    some (feltBitAnd x0 128 * 1997537281) = y16 ∧ some (feltBitAnd x0 127) = y17  := by
    rewrite [part31_cumulative_wp]
    unfold part31_state_update
    unfold part31_state
    MLIR_states_updates'
    -- 1 withEqZero
    rewrite [withEqZero_def]
    MLIR_states_updates'
    unfold part31_drops
    -- 5 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    unfold Code.getReturn
    simp only
    simp [Map.update_get_wobbly, List.getLast!]
end Risc0.ComputeDecode.Witness.WP