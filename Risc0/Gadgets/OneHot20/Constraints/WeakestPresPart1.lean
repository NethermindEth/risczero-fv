import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart0

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part1 on st
def part1_state (st: State) : State :=
  
        ((((st["%21"] ←ₛ
                getImpl st { name := "data" : BufferVar } (0 : Back) (1 : ℕ))[felts][{ name := "%24" : FeltVar }] ←
              Option.get!
                  (State.felts (st["%21"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (1 : ℕ))
                    { name := "%21" : FeltVar }) +
                Option.get! (State.felts st { name := "%23" : FeltVar }))[felts][{ name := "%2" : FeltVar }] ←
            (3 : Felt))["%25"] ←ₛ
          getImpl st { name := "data" : BufferVar } (0 : Back) (3 : ℕ)) 

def part1_drops (st: State) : State :=
  State.dropFelts (st) ⟨"%23"⟩

-- Run the program from part1 onwards by using part1_state rather than Code.part1
def part1_state_update (st: State): State :=
  Γ (part1_drops (part1_state st)) ⟦Code.part2;dropfelt ⟨"%24"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%26"⟩;Code.part3;dropfelt ⟨"%27"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%29"⟩;Code.part4;dropfelt ⟨"%30"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%32"⟩;Code.part5;dropfelt ⟨"%33"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%35"⟩;Code.part6;dropfelt ⟨"%36"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%38"⟩;Code.part7;dropfelt ⟨"%39"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%41"⟩;Code.part8;dropfelt ⟨"%42"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%44"⟩;Code.part9;dropfelt ⟨"%45"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%47"⟩;Code.part10;dropfelt ⟨"%48"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%50"⟩;Code.part11;dropfelt ⟨"%51"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%53"⟩;Code.part12;dropfelt ⟨"%54"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%56"⟩;Code.part13;dropfelt ⟨"%57"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%59"⟩;Code.part14;dropfelt ⟨"%60"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%62"⟩;Code.part15;dropfelt ⟨"%63"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%65"⟩;Code.part16;dropfelt ⟨"%66"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%68"⟩;Code.part17;dropfelt ⟨"%69"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%71"⟩;Code.part18;dropfelt ⟨"%72"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%20"⟩;Code.part19;dropfelt ⟨"%76"⟩;Code.part20;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%82"⟩;Code.part21;dropfelt ⟨"%21"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%86"⟩;Code.part22;dropfelt ⟨"%22"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%90"⟩;Code.part23;dropfelt ⟨"%25"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%94"⟩;Code.part24;dropfelt ⟨"%28"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%98"⟩;Code.part25;dropfelt ⟨"%31"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%102"⟩;Code.part26;dropfelt ⟨"%34"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%106"⟩;Code.part27;dropfelt ⟨"%37"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%110"⟩;Code.part28;dropfelt ⟨"%40"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%111"⟩;dropfelt ⟨"%114"⟩;Code.part29;dropfelt ⟨"%43"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%118"⟩;Code.part30;dropfelt ⟨"%46"⟩;dropfelt ⟨"%117"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%122"⟩;Code.part31;dropfelt ⟨"%49"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%123"⟩;dropfelt ⟨"%126"⟩;Code.part32;dropfelt ⟨"%52"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%130"⟩;Code.part33;dropfelt ⟨"%55"⟩;dropfelt ⟨"%129"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%134"⟩;Code.part34;dropfelt ⟨"%58"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%135"⟩;dropfelt ⟨"%138"⟩;Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%19"⟩;dropfelt ⟨"%73"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%108"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%120"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%132"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%140"⟩;dropfelt ⟨"%144"⟩;dropfelt ⟨"%148"⟩;dropfelt ⟨"%152"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;dropfelt ⟨"%159"⟩⟧

-- Prove that substituting part1_state for Code.part1 produces the same result
lemma part1_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part1;dropfelt ⟨"%23"⟩;Code.part2;dropfelt ⟨"%24"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%26"⟩;Code.part3;dropfelt ⟨"%27"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%29"⟩;Code.part4;dropfelt ⟨"%30"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%32"⟩;Code.part5;dropfelt ⟨"%33"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%35"⟩;Code.part6;dropfelt ⟨"%36"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%38"⟩;Code.part7;dropfelt ⟨"%39"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%41"⟩;Code.part8;dropfelt ⟨"%42"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%44"⟩;Code.part9;dropfelt ⟨"%45"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%47"⟩;Code.part10;dropfelt ⟨"%48"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%50"⟩;Code.part11;dropfelt ⟨"%51"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%53"⟩;Code.part12;dropfelt ⟨"%54"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%56"⟩;Code.part13;dropfelt ⟨"%57"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%59"⟩;Code.part14;dropfelt ⟨"%60"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%62"⟩;Code.part15;dropfelt ⟨"%63"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%65"⟩;Code.part16;dropfelt ⟨"%66"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%68"⟩;Code.part17;dropfelt ⟨"%69"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%71"⟩;Code.part18;dropfelt ⟨"%72"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%20"⟩;Code.part19;dropfelt ⟨"%76"⟩;Code.part20;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%82"⟩;Code.part21;dropfelt ⟨"%21"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%86"⟩;Code.part22;dropfelt ⟨"%22"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%90"⟩;Code.part23;dropfelt ⟨"%25"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%94"⟩;Code.part24;dropfelt ⟨"%28"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%98"⟩;Code.part25;dropfelt ⟨"%31"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%102"⟩;Code.part26;dropfelt ⟨"%34"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%106"⟩;Code.part27;dropfelt ⟨"%37"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%110"⟩;Code.part28;dropfelt ⟨"%40"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%111"⟩;dropfelt ⟨"%114"⟩;Code.part29;dropfelt ⟨"%43"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%118"⟩;Code.part30;dropfelt ⟨"%46"⟩;dropfelt ⟨"%117"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%122"⟩;Code.part31;dropfelt ⟨"%49"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%123"⟩;dropfelt ⟨"%126"⟩;Code.part32;dropfelt ⟨"%52"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%130"⟩;Code.part33;dropfelt ⟨"%55"⟩;dropfelt ⟨"%129"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%134"⟩;Code.part34;dropfelt ⟨"%58"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%135"⟩;dropfelt ⟨"%138"⟩;Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%19"⟩;dropfelt ⟨"%73"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%108"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%120"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%132"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%140"⟩;dropfelt ⟨"%144"⟩;dropfelt ⟨"%148"⟩;dropfelt ⟨"%152"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;dropfelt ⟨"%159"⟩) st) ↔
  Code.getReturn (part1_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%23"⟩;Code.part2;dropfelt ⟨"%24"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%26"⟩;Code.part3;dropfelt ⟨"%27"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%29"⟩;Code.part4;dropfelt ⟨"%30"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%32"⟩;Code.part5;dropfelt ⟨"%33"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%35"⟩;Code.part6;dropfelt ⟨"%36"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%38"⟩;Code.part7;dropfelt ⟨"%39"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%41"⟩;Code.part8;dropfelt ⟨"%42"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%44"⟩;Code.part9;dropfelt ⟨"%45"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%47"⟩;Code.part10;dropfelt ⟨"%48"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%50"⟩;Code.part11;dropfelt ⟨"%51"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%53"⟩;Code.part12;dropfelt ⟨"%54"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%56"⟩;Code.part13;dropfelt ⟨"%57"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%59"⟩;Code.part14;dropfelt ⟨"%60"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%62"⟩;Code.part15;dropfelt ⟨"%63"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%65"⟩;Code.part16;dropfelt ⟨"%66"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%68"⟩;Code.part17;dropfelt ⟨"%69"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%71"⟩;Code.part18;dropfelt ⟨"%72"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%20"⟩;Code.part19;dropfelt ⟨"%76"⟩;Code.part20;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%82"⟩;Code.part21;dropfelt ⟨"%21"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%86"⟩;Code.part22;dropfelt ⟨"%22"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%90"⟩;Code.part23;dropfelt ⟨"%25"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%94"⟩;Code.part24;dropfelt ⟨"%28"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%98"⟩;Code.part25;dropfelt ⟨"%31"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%102"⟩;Code.part26;dropfelt ⟨"%34"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%106"⟩;Code.part27;dropfelt ⟨"%37"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%110"⟩;Code.part28;dropfelt ⟨"%40"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%111"⟩;dropfelt ⟨"%114"⟩;Code.part29;dropfelt ⟨"%43"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%118"⟩;Code.part30;dropfelt ⟨"%46"⟩;dropfelt ⟨"%117"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%122"⟩;Code.part31;dropfelt ⟨"%49"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%123"⟩;dropfelt ⟨"%126"⟩;Code.part32;dropfelt ⟨"%52"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%130"⟩;Code.part33;dropfelt ⟨"%55"⟩;dropfelt ⟨"%129"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%134"⟩;Code.part34;dropfelt ⟨"%58"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%135"⟩;dropfelt ⟨"%138"⟩;Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%19"⟩;dropfelt ⟨"%73"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%108"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%120"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%132"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%140"⟩;dropfelt ⟨"%144"⟩;dropfelt ⟨"%148"⟩;dropfelt ⟨"%152"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;dropfelt ⟨"%159"⟩) = prog
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
                  ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                      [[some y0, some y1, some y2, some y3, some y4, some y5, some y6, some y7, some y8, some y9,
                          some y10, some y11, some y12, some y13, some y14, some y15, some y16, some y17, some y18,
                          some y19]])[{ name := "code" : BufferVar }] ←ₘ
                    [[some x0]],
                bufferWidths :=
                  ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                      (20 : ℕ))[{ name := "code" : BufferVar }] ←ₘ
                    (1 : ℕ),
                constraints := [], cycle := (0 : ℕ), felts := Map.empty, isFailed := false, props := Map.empty,
                vars :=
                  [{ name := "code" : BufferVar },
                    { name := "data" : BufferVar }] }[props][{ name := "%19" : PropVar }] ←
              True)[felts][{ name := "%22" : FeltVar }] ←
            y2)[felts][{ name := "%23" : FeltVar }] ←
          y2 * (2 : Felt)))  := by
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

end Risc0.OneHot20.Constraints.WP