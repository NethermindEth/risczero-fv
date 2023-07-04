import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart4

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part5 on st
def part5_state (st: State) : State :=
  
          ((((State.set! st { name := "data" } 8 (Option.get! st.felts[({ name := "%81" }: FeltVar)]!))[felts][{ name := "%10" }] ←
                6)[felts][{ name := "%82" }] ←
              feltBitAnd (Option.get! (State.felts st { name := "%23" })) 6)[felts][{ name := "%9" }] ←
            1006632961) 

def part5_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (st) ⟨"%81"⟩) ⟨"%10"⟩

-- Run the program from part5 onwards by using part5_state rather than Code.part5
def part5_state_update (st: State): State :=
  Γ (part5_drops (part5_state st)) ⟦Code.part6;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;Code.part7;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;Code.part8;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;Code.part9;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part10;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;Code.part11;dropfelt ⟨"%93"⟩;Code.part12;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;Code.part13;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;Code.part14;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part15;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;Code.part16;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;Code.part17;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;Code.part18;dropfelt ⟨"%26"⟩;Code.part19;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;Code.part20;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;Code.part21;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;Code.part22;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;Code.part23;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part24;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;Code.part25;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;Code.part26;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;Code.part27;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;Code.part28;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩⟧

-- Prove that substituting part5_state for Code.part5 produces the same result
lemma part5_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part5;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;Code.part6;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;Code.part7;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;Code.part8;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;Code.part9;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part10;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;Code.part11;dropfelt ⟨"%93"⟩;Code.part12;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;Code.part13;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;Code.part14;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part15;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;Code.part16;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;Code.part17;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;Code.part18;dropfelt ⟨"%26"⟩;Code.part19;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;Code.part20;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;Code.part21;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;Code.part22;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;Code.part23;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part24;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;Code.part25;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;Code.part26;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;Code.part27;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;Code.part28;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part5_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;Code.part6;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;Code.part7;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;Code.part8;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;Code.part9;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part10;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;Code.part11;dropfelt ⟨"%93"⟩;Code.part12;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;Code.part13;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;Code.part14;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part15;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;Code.part16;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;Code.part17;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;Code.part18;dropfelt ⟨"%26"⟩;Code.part19;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;Code.part20;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;Code.part21;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;Code.part22;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;Code.part23;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part24;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;Code.part25;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;Code.part26;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;Code.part27;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;Code.part28;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) = prog
  unfold Code.part5
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part5_state_update part5_drops part5_state
  rfl

lemma part5_updates_opaque {st : State} : 
  Code.getReturn (part4_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part5_state_update (part4_drops (part4_state st))) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part4_state_update, part5_wp]

lemma part5_cumulative_wp {x0 x1 x2 x3: Felt} :
  Code.run (start_state [x0,x1,x2,x3]) = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17] ↔
  Code.getReturn
        (part5_state_update
          (({
                buffers :=
                  ((fun x => Map.empty x)[{ name := "in" }] ←ₘ
                      [[some x0, some x1, some x2, some x3]])[{ name := "data" }] ←ₘ
                    [[none, some (feltBitAnd x3 96 * 1950351361), none, none, none, none, none, none, none,
                        some (feltBitAnd x3 16 * 1887436801), some (feltBitAnd x3 128 * 1997537281), none, none, none,
                        none, none, none, none]],
                bufferWidths := ((fun x => Map.empty x)[{ name := "data" }] ←ₘ 18)[{ name := "in" }] ←ₘ 4,
                constraints := [], cycle := 0,
                felts :=
                  ((((((Map.empty[{ name := "%19" }] ←ₘ 128)[{ name := "%23" }] ←ₘ x3)[{ name := "%18" }] ←ₘ
                            1997537281)[{ name := "%17" }] ←ₘ
                          96)[{ name := "%16" }] ←ₘ
                        1950351361)[{ name := "%15" }] ←ₘ
                      16)[{ name := "%14" }] ←ₘ
                    1887436801,
                isFailed := false, props := Map.empty,
                vars := [{ name := "in" }, { name := "data" }] }[felts][{ name := "%13" }] ←
              8)[felts][{ name := "%81" }] ←
            feltBitAnd x3 8 * 1761607681)) =
      [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17]  := by
    rewrite [part4_cumulative_wp]
    rewrite [part5_updates_opaque]
    unfold part4_state
    MLIR_states_updates'
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates'
    unfold part4_drops
    -- 2 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

end Risc0.ComputeDecode.Witness.WP