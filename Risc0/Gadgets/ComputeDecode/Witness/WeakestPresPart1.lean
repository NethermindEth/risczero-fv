import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart0

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part1 on st
def part1_state (st: State) : State :=
  
          (((State.set!
                (st[felts][{ name := "%75" }] ←
                  Option.get! (State.felts st { name := "%74" }) * Option.get! (State.felts st { name := "%18" }))
                { name := "data" } 10
                (Option.get! (State.felts st { name := "%74" }) *
                  Option.get! (State.felts st { name := "%18" })))[felts][{ name := "%17" }] ←
              96)[felts][{ name := "%76" }] ←
            feltBitAnd (Option.get! (State.felts st { name := "%23" })) 96) 

def part1_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (st) ⟨"%74"⟩) ⟨"%75"⟩

-- Run the program from part1 onwards by using part1_state rather than Code.part1
def part1_state_update (st: State): State :=
  Γ (part1_drops (part1_state st)) ⟦Code.part2;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;Code.part3;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part4;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;Code.part5;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;Code.part6;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;Code.part7;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;Code.part8;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;Code.part9;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part10;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;Code.part11;dropfelt ⟨"%93"⟩;Code.part12;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;Code.part13;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;Code.part14;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part15;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;Code.part16;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;Code.part17;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;Code.part18;dropfelt ⟨"%26"⟩;Code.part19;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;Code.part20;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;Code.part21;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;Code.part22;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;Code.part23;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part24;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;Code.part25;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;Code.part26;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;Code.part27;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;Code.part28;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩⟧

-- Prove that substituting part1_state for Code.part1 produces the same result
lemma part1_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part1;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;Code.part2;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;Code.part3;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part4;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;Code.part5;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;Code.part6;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;Code.part7;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;Code.part8;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;Code.part9;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part10;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;Code.part11;dropfelt ⟨"%93"⟩;Code.part12;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;Code.part13;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;Code.part14;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part15;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;Code.part16;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;Code.part17;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;Code.part18;dropfelt ⟨"%26"⟩;Code.part19;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;Code.part20;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;Code.part21;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;Code.part22;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;Code.part23;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part24;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;Code.part25;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;Code.part26;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;Code.part27;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;Code.part28;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part1_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;Code.part2;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;Code.part3;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part4;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;Code.part5;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;Code.part6;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;Code.part7;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;Code.part8;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;Code.part9;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part10;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;Code.part11;dropfelt ⟨"%93"⟩;Code.part12;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;Code.part13;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;Code.part14;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part15;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;Code.part16;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;Code.part17;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;Code.part18;dropfelt ⟨"%26"⟩;Code.part19;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;Code.part20;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;Code.part21;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;Code.part22;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;Code.part23;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part24;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;Code.part25;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;Code.part26;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;Code.part27;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;Code.part28;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) = prog
  unfold Code.part1
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part1_state_update part1_drops part1_state
  rfl

lemma part1_updates_opaque {st : State} : 
  Code.getReturn (part0_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part1_state_update (part0_drops (part0_state st))) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part0_state_update, part1_wp]

end Risc0.ComputeDecode.Witness.WP