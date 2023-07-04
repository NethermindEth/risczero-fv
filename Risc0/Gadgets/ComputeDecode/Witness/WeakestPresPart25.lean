import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart24

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part25 on st
def part25_state (st: State) : State :=
  
          ((((st[felts][{ name := "%50" }] ←
                  Option.get! (State.felts st { name := "%49" }) +
                    Option.get! (State.felts st { name := "%44" }))[felts][{ name := "%51" }] ←
                (Option.get! (State.felts st { name := "%49" }) + Option.get! (State.felts st { name := "%44" })) *
                  Option.get! (State.felts st { name := "%15" }))[felts][{ name := "%52" }] ←
              (Option.get! (State.felts st { name := "%49" }) + Option.get! (State.felts st { name := "%44" })) *
                  Option.get! (State.felts st { name := "%15" }) +
                Option.get! (State.felts st { name := "%43" }))["%41"] ←ₛ
            getImpl st { name := "data" } 0 3) 

def part25_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%43"⟩) ⟨"%49"⟩) ⟨"%44"⟩) ⟨"%50"⟩) ⟨"%51"⟩

-- Run the program from part25 onwards by using part25_state rather than Code.part25
def part25_state_update (st: State): State :=
  Γ (part25_drops (part25_state st)) ⟦Code.part26;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;Code.part27;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;Code.part28;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩⟧

-- Prove that substituting part25_state for Code.part25 produces the same result
lemma part25_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part25;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;Code.part26;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;Code.part27;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;Code.part28;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part25_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;Code.part26;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;Code.part27;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;Code.part28;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) = prog
  unfold Code.part25
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part25_state_update part25_drops part25_state
  rfl

lemma part25_updates_opaque {st : State} : 
  Code.getReturn (part24_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part25_state_update (part24_drops (part24_state st))) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part24_state_update, part25_wp]

lemma part25_cumulative_wp {x0 x1 x2 x3: Felt} :
  Code.run (start_state [x0,x1,x2,x3]) = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17] ↔
  Code.getReturn
        (part25_state_update
          ((({
                  buffers :=
                    ((fun x => Map.empty x)[{ name := "in" }] ←ₘ
                        [[some x0, some x1, some x2, some x3]])[{ name := "data" }] ←ₘ
                      [[some (feltBitAnd x3 6 * 1006632961), some (feltBitAnd x3 96 * 1950351361),
                          some (feltBitAnd x2 96 * 1950351361), some (feltBitAnd x2 3),
                          some (feltBitAnd x2 12 * 1509949441), some (feltBitAnd x1 48 * 1887436801),
                          some (feltBitAnd x1 3), some (feltBitAnd x1 12 * 1509949441),
                          some (feltBitAnd x3 8 * 1761607681), some (feltBitAnd x3 16 * 1887436801),
                          some (feltBitAnd x3 128 * 1997537281), some (feltBitAnd x2 16 * 1887436801),
                          some (feltBitAnd x2 128 * 1997537281), some (feltBitAnd x3 1),
                          some (feltBitAnd x1 128 * 1997537281), some (feltBitAnd x1 64 * 1981808641),
                          some (feltBitAnd x0 128 * 1997537281), some (feltBitAnd x0 127)]],
                  bufferWidths := ((fun x => Map.empty x)[{ name := "data" }] ←ₘ 18)[{ name := "in" }] ←ₘ 4,
                  constraints :=
                    [x3 -
                          ((feltBitAnd x3 128 * 1997537281 * 64 +
                                (feltBitAnd x3 96 * 1950351361 * 16 + feltBitAnd x3 16 * 1887436801 * 8 +
                                    feltBitAnd x3 8 * 1761607681 * 4 +
                                  feltBitAnd x3 6 * 1006632961)) *
                              2 +
                            feltBitAnd x3 1) =
                        0],
                  cycle := 0,
                  felts :=
                    (((((Map.empty[{ name := "%19" }] ←ₘ 128)[{ name := "%15" }] ←ₘ 16)[{ name := "%22" }] ←ₘ
                            x2)[{ name := "%21" }] ←ₘ
                          x1)[{ name := "%20" }] ←ₘ
                        x0)[{ name := "%7" }] ←ₘ
                      4,
                  isFailed := false, props := Map.empty,
                  vars := [{ name := "in" }, { name := "data" }] }[felts][{ name := "%43" }] ←
                feltBitAnd x2 12 * 1509949441 * 4)[felts][{ name := "%49" }] ←
              feltBitAnd x2 128 * 1997537281 * 8 + feltBitAnd x2 96 * 1950351361 * 2)[felts][{ name := "%44" }] ←
            feltBitAnd x2 16 * 1887436801)) =
      [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17]  := by
    rewrite [part24_cumulative_wp]
    rewrite [part25_updates_opaque]
    unfold part24_state
    MLIR_states_updates'
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates'
    unfold part24_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

end Risc0.ComputeDecode.Witness.WP