import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart6

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part7 on st
def part7_state (st: State) : State :=
  
          ((State.set!
              ((st[felts][{ name := "%151" : FeltVar }] ←
                  Option.get! (State.felts st { name := "%20" : FeltVar }) -
                    Option.get! (State.felts st { name := "%12" : FeltVar }))[felts][{ name := "%152" : FeltVar }] ←
                if
                    Option.get! (State.felts st { name := "%20" : FeltVar }) -
                        Option.get! (State.felts st { name := "%12" : FeltVar }) =
                      (0 : Felt) then
                  (1 : Felt)
                else (0 : Felt))
              { name := "data" : BufferVar } (7 : ℕ)
              (if
                  Option.get! (State.felts st { name := "%20" : FeltVar }) -
                      Option.get! (State.felts st { name := "%12" : FeltVar }) =
                    (0 : Felt) then
                (1 : Felt)
              else (0 : Felt)))[felts][{ name := "%11" : FeltVar }] ←
            (8 : Felt)) 

def part7_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (st) ⟨"%151"⟩) ⟨"%152"⟩

-- Run the program from part7 onwards by using part7_state rather than Code.part7
def part7_state_update (st: State): State :=
  Γ (part7_drops (part7_state st)) ⟦Code.part8;dropfelt ⟨"%153"⟩;dropfelt ⟨"%154"⟩;Code.part9;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;Code.part10;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;Code.part11;dropfelt ⟨"%159"⟩;dropfelt ⟨"%160"⟩;Code.part12;dropfelt ⟨"%161"⟩;dropfelt ⟨"%162"⟩;Code.part13;dropfelt ⟨"%163"⟩;dropfelt ⟨"%164"⟩;Code.part14;dropfelt ⟨"%165"⟩;dropfelt ⟨"%166"⟩;Code.part15;dropfelt ⟨"%167"⟩;dropfelt ⟨"%168"⟩;Code.part16;dropfelt ⟨"%169"⟩;dropfelt ⟨"%170"⟩;Code.part17;dropfelt ⟨"%171"⟩;dropfelt ⟨"%172"⟩;Code.part18;dropfelt ⟨"%173"⟩;dropfelt ⟨"%174"⟩;Code.part19;dropfelt ⟨"%175"⟩;dropfelt ⟨"%176"⟩;Code.part20;dropfelt ⟨"%17"⟩;dropfelt ⟨"%23"⟩;Code.part21;dropfelt ⟨"%16"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%26"⟩;Code.part22;dropfelt ⟨"%14"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%32"⟩;Code.part23;dropfelt ⟨"%13"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%35"⟩;Code.part24;dropfelt ⟨"%12"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%38"⟩;Code.part25;dropfelt ⟨"%10"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%44"⟩;Code.part26;dropfelt ⟨"%9"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%47"⟩;Code.part27;dropfelt ⟨"%8"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%50"⟩;Code.part28;dropfelt ⟨"%6"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%56"⟩;Code.part29;dropfelt ⟨"%5"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%59"⟩;Code.part30;dropfelt ⟨"%4"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%62"⟩;Code.part31;dropfelt ⟨"%2"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%68"⟩;Code.part32;dropfelt ⟨"%1"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%71"⟩;Code.part33;dropfelt ⟨"%20"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;Code.part34;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩⟧

-- Prove that substituting part7_state for Code.part7 produces the same result
lemma part7_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part7;dropfelt ⟨"%151"⟩;dropfelt ⟨"%152"⟩;Code.part8;dropfelt ⟨"%153"⟩;dropfelt ⟨"%154"⟩;Code.part9;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;Code.part10;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;Code.part11;dropfelt ⟨"%159"⟩;dropfelt ⟨"%160"⟩;Code.part12;dropfelt ⟨"%161"⟩;dropfelt ⟨"%162"⟩;Code.part13;dropfelt ⟨"%163"⟩;dropfelt ⟨"%164"⟩;Code.part14;dropfelt ⟨"%165"⟩;dropfelt ⟨"%166"⟩;Code.part15;dropfelt ⟨"%167"⟩;dropfelt ⟨"%168"⟩;Code.part16;dropfelt ⟨"%169"⟩;dropfelt ⟨"%170"⟩;Code.part17;dropfelt ⟨"%171"⟩;dropfelt ⟨"%172"⟩;Code.part18;dropfelt ⟨"%173"⟩;dropfelt ⟨"%174"⟩;Code.part19;dropfelt ⟨"%175"⟩;dropfelt ⟨"%176"⟩;Code.part20;dropfelt ⟨"%17"⟩;dropfelt ⟨"%23"⟩;Code.part21;dropfelt ⟨"%16"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%26"⟩;Code.part22;dropfelt ⟨"%14"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%32"⟩;Code.part23;dropfelt ⟨"%13"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%35"⟩;Code.part24;dropfelt ⟨"%12"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%38"⟩;Code.part25;dropfelt ⟨"%10"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%44"⟩;Code.part26;dropfelt ⟨"%9"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%47"⟩;Code.part27;dropfelt ⟨"%8"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%50"⟩;Code.part28;dropfelt ⟨"%6"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%56"⟩;Code.part29;dropfelt ⟨"%5"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%59"⟩;Code.part30;dropfelt ⟨"%4"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%62"⟩;Code.part31;dropfelt ⟨"%2"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%68"⟩;Code.part32;dropfelt ⟨"%1"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%71"⟩;Code.part33;dropfelt ⟨"%20"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;Code.part34;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part7_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%151"⟩;dropfelt ⟨"%152"⟩;Code.part8;dropfelt ⟨"%153"⟩;dropfelt ⟨"%154"⟩;Code.part9;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;Code.part10;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;Code.part11;dropfelt ⟨"%159"⟩;dropfelt ⟨"%160"⟩;Code.part12;dropfelt ⟨"%161"⟩;dropfelt ⟨"%162"⟩;Code.part13;dropfelt ⟨"%163"⟩;dropfelt ⟨"%164"⟩;Code.part14;dropfelt ⟨"%165"⟩;dropfelt ⟨"%166"⟩;Code.part15;dropfelt ⟨"%167"⟩;dropfelt ⟨"%168"⟩;Code.part16;dropfelt ⟨"%169"⟩;dropfelt ⟨"%170"⟩;Code.part17;dropfelt ⟨"%171"⟩;dropfelt ⟨"%172"⟩;Code.part18;dropfelt ⟨"%173"⟩;dropfelt ⟨"%174"⟩;Code.part19;dropfelt ⟨"%175"⟩;dropfelt ⟨"%176"⟩;Code.part20;dropfelt ⟨"%17"⟩;dropfelt ⟨"%23"⟩;Code.part21;dropfelt ⟨"%16"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%26"⟩;Code.part22;dropfelt ⟨"%14"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%32"⟩;Code.part23;dropfelt ⟨"%13"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%35"⟩;Code.part24;dropfelt ⟨"%12"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%38"⟩;Code.part25;dropfelt ⟨"%10"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%44"⟩;Code.part26;dropfelt ⟨"%9"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%47"⟩;Code.part27;dropfelt ⟨"%8"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%50"⟩;Code.part28;dropfelt ⟨"%6"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%56"⟩;Code.part29;dropfelt ⟨"%5"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%59"⟩;Code.part30;dropfelt ⟨"%4"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%62"⟩;Code.part31;dropfelt ⟨"%2"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%68"⟩;Code.part32;dropfelt ⟨"%1"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%71"⟩;Code.part33;dropfelt ⟨"%20"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;Code.part34;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) = prog
  unfold Code.part7
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part7_state_update part7_drops part7_state
  rfl

lemma part7_updates_opaque {st : State} : 
  Code.getReturn (part6_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part7_state_update (part6_drops (part6_state st))) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part6_state_update, part7_wp]

set_option maxRecDepth 10000000 in
lemma part7_cumulative_wp {x0: Felt} :
  Code.run (start_state [x0]) = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19] ↔
  Code.getReturn
        (part7_state_update
          ({
              buffers :=
                (Map.empty[{ name := "code" : BufferVar }] ←ₘ [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                  [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (2 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (3 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (4 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (5 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (6 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)), none, none, none, none,
                      none, none, none, none, none, none, none, none, none]],
              bufferWidths :=
                ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ (20 : ℕ))[{ name := "code" : BufferVar }] ←ₘ
                  (1 : ℕ),
              constraints := [], cycle := (0 : ℕ),
              felts :=
                ((((((Map.empty[{ name := "%20" : FeltVar }] ←ₘ x0)[{ name := "%18" : FeltVar }] ←ₘ
                            (1 : Felt))[{ name := "%17" : FeltVar }] ←ₘ
                          (2 : Felt))[{ name := "%16" : FeltVar }] ←ₘ
                        (3 : Felt))[{ name := "%15" : FeltVar }] ←ₘ
                      (4 : Felt))[{ name := "%14" : FeltVar }] ←ₘ
                    (5 : Felt))[{ name := "%13" : FeltVar }] ←ₘ
                  (6 : Felt),
              isFailed := false, props := Map.empty,
              vars :=
                [{ name := "code" : BufferVar }, { name := "data" : BufferVar }] }[felts][{ name := "%12" : FeltVar }] ←
            (7 : Felt))) =
      [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19]  := by
    rewrite [part6_cumulative_wp]
    rewrite [part7_updates_opaque]
    unfold part6_state
    try simplify_get_hack
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part6_drops
    -- 2 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 1 set
    rewrite [Map.drop_of_updates]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.constraints_if_eq_if_constraints,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.OneHot20.Witness.WP