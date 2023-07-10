import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart20

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part21 on st
def part21_state (st: State) : State :=
  
          ((((st[felts][{ name := "%36" }] ←
                  Option.get! (State.felts st { name := "%35" }) *
                    Option.get! (State.felts st { name := "%3" }))[felts][{ name := "%37" }] ←
                Option.get! (State.felts st { name := "%35" }) * Option.get! (State.felts st { name := "%3" }) +
                  Option.get! (State.felts st { name := "%34" }))[felts][{ name := "%11" }] ←
              (2 : Felt))[felts][{ name := "%38" }] ←
            (Option.get! (State.felts st { name := "%35" }) * Option.get! (State.felts st { name := "%3" }) +
                Option.get! (State.felts st { name := "%34" })) *
              (2 : Felt)) 

def part21_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%3"⟩) ⟨"%34"⟩) ⟨"%35"⟩) ⟨"%36"⟩) ⟨"%37"⟩

-- Run the program from part21 onwards by using part21_state rather than Code.part21
def part21_state_update (st: State): State :=
  Γ (part21_drops (part21_state st)) ⟦Code.part22;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;Code.part23;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part24;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;Code.part25;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;Code.part26;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;Code.part27;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;Code.part28;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩⟧

-- Prove that substituting part21_state for Code.part21 produces the same result
lemma part21_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part21;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;Code.part22;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;Code.part23;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part24;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;Code.part25;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;Code.part26;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;Code.part27;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;Code.part28;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part21_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;Code.part22;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;Code.part23;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part24;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;Code.part25;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;Code.part26;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;Code.part27;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;Code.part28;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) = prog
  unfold Code.part21
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part21_state_update part21_drops part21_state
  rfl

lemma part21_updates_opaque {st : State} : 
  Code.getReturn (part20_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part21_state_update (part20_drops (part20_state st))) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part20_state_update, part21_wp]

lemma part21_cumulative_wp {x0 x1 x2 x3: Felt} :
  Code.run (start_state [x0,x1,x2,x3]) = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17] ↔
  Code.getReturn
        (part21_state_update
          ((({
                  buffers :=
                    ((fun x => Map.empty x)[{ name := "in" }] ←ₘ
                        [[some x0, some x1, some x2, some x3]])[{ name := "data" }] ←ₘ
                      [[some (feltBitAnd x3 (6 : Felt) * (1006632961 : Felt)),
                          some (feltBitAnd x3 (96 : Felt) * (1950351361 : Felt)),
                          some (feltBitAnd x2 (96 : Felt) * (1950351361 : Felt)), some (feltBitAnd x2 (3 : Felt)),
                          some (feltBitAnd x2 (12 : Felt) * (1509949441 : Felt)),
                          some (feltBitAnd x1 (48 : Felt) * (1887436801 : Felt)), some (feltBitAnd x1 (3 : Felt)),
                          some (feltBitAnd x1 (12 : Felt) * (1509949441 : Felt)),
                          some (feltBitAnd x3 (8 : Felt) * (1761607681 : Felt)),
                          some (feltBitAnd x3 (16 : Felt) * (1887436801 : Felt)),
                          some (feltBitAnd x3 (128 : Felt) * (1997537281 : Felt)),
                          some (feltBitAnd x2 (16 : Felt) * (1887436801 : Felt)),
                          some (feltBitAnd x2 (128 : Felt) * (1997537281 : Felt)), some (feltBitAnd x3 (1 : Felt)),
                          some (feltBitAnd x1 (128 : Felt) * (1997537281 : Felt)),
                          some (feltBitAnd x1 (64 : Felt) * (1981808641 : Felt)),
                          some (feltBitAnd x0 (128 : Felt) * (1997537281 : Felt)), some (feltBitAnd x0 (127 : Felt))]],
                  bufferWidths := ((fun x => Map.empty x)[{ name := "data" }] ←ₘ (18 : ℕ))[{ name := "in" }] ←ₘ (4 : ℕ),
                  constraints := [], cycle := (0 : ℕ),
                  felts :=
                    (((((((Map.empty[{ name := "%19" }] ←ₘ (128 : Felt))[{ name := "%23" }] ←ₘ x3)[{ name := "%15" }] ←ₘ
                                (16 : Felt))[{ name := "%13" }] ←ₘ
                              (8 : Felt))[{ name := "%22" }] ←ₘ
                            x2)[{ name := "%21" }] ←ₘ
                          x1)[{ name := "%3" }] ←ₘ
                        (64 : Felt))[{ name := "%20" }] ←ₘ
                      x0,
                  isFailed := false, props := Map.empty,
                  vars := [{ name := "in" }, { name := "data" }] }[felts][{ name := "%7" }] ←
                (4 : Felt))[felts][{ name := "%34" }] ←
              feltBitAnd x3 (96 : Felt) * (1950351361 : Felt) * (16 : Felt) +
                    feltBitAnd x3 (16 : Felt) * (1887436801 : Felt) * (8 : Felt) +
                  feltBitAnd x3 (8 : Felt) * (1761607681 : Felt) * (4 : Felt) +
                feltBitAnd x3 (6 : Felt) * (1006632961 : Felt))[felts][{ name := "%35" }] ←
            feltBitAnd x3 (128 : Felt) * (1997537281 : Felt))) =
      [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17]  := by
    rewrite [part20_cumulative_wp]
    rewrite [part21_updates_opaque]
    unfold part20_state
    try simplify_get_hack
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part20_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

end Risc0.ComputeDecode.Witness.WP