import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.CodeDrops

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part0 on st
def part0_state (st: State) : State :=
  
        ((State.set!
            ((st["%20"] ←ₛ
                getImpl st { name := "code" : BufferVar } (0 : Back) (0 : ℕ))[felts][{ name := "%138" : FeltVar }] ←
              if
                  Option.get!
                      (State.felts (st["%20"] ←ₛ getImpl st { name := "code" : BufferVar } (0 : Back) (0 : ℕ))
                        { name := "%20" : FeltVar }) =
                    (0 : Felt) then
                (1 : Felt)
              else (0 : Felt))
            { name := "data" : BufferVar } (0 : ℕ)
            (if
                Option.get!
                    (State.felts (st["%20"] ←ₛ getImpl st { name := "code" : BufferVar } (0 : Back) (0 : ℕ))
                      { name := "%20" : FeltVar }) =
                  (0 : Felt) then
              (1 : Felt)
            else (0 : Felt)))[felts][{ name := "%18" : FeltVar }] ←
          (1 : Felt)) 

def part0_drops (st: State) : State :=
  State.dropFelts (st) ⟨"%138"⟩

-- Run the whole program by using part0_state rather than Code.part0
def part0_state_update (st: State): State :=
  Γ (part0_drops (part0_state st)) ⟦Code.part1;dropfelt ⟨"%139"⟩;dropfelt ⟨"%140"⟩;Code.part2;dropfelt ⟨"%141"⟩;dropfelt ⟨"%142"⟩;Code.part3;dropfelt ⟨"%143"⟩;dropfelt ⟨"%144"⟩;Code.part4;dropfelt ⟨"%145"⟩;dropfelt ⟨"%146"⟩;Code.part5;dropfelt ⟨"%147"⟩;dropfelt ⟨"%148"⟩;Code.part6;dropfelt ⟨"%149"⟩;dropfelt ⟨"%150"⟩;Code.part7;dropfelt ⟨"%151"⟩;dropfelt ⟨"%152"⟩;Code.part8;dropfelt ⟨"%153"⟩;dropfelt ⟨"%154"⟩;Code.part9;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;Code.part10;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;Code.part11;dropfelt ⟨"%159"⟩;dropfelt ⟨"%160"⟩;Code.part12;dropfelt ⟨"%161"⟩;dropfelt ⟨"%162"⟩;Code.part13;dropfelt ⟨"%163"⟩;dropfelt ⟨"%164"⟩;Code.part14;dropfelt ⟨"%165"⟩;dropfelt ⟨"%166"⟩;Code.part15;dropfelt ⟨"%167"⟩;dropfelt ⟨"%168"⟩;Code.part16;dropfelt ⟨"%169"⟩;dropfelt ⟨"%170"⟩;Code.part17;dropfelt ⟨"%171"⟩;dropfelt ⟨"%172"⟩;Code.part18;dropfelt ⟨"%173"⟩;dropfelt ⟨"%174"⟩;Code.part19;dropfelt ⟨"%175"⟩;dropfelt ⟨"%176"⟩;Code.part20;dropfelt ⟨"%17"⟩;dropfelt ⟨"%23"⟩;Code.part21;dropfelt ⟨"%16"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%26"⟩;Code.part22;dropfelt ⟨"%14"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%32"⟩;Code.part23;dropfelt ⟨"%13"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%35"⟩;Code.part24;dropfelt ⟨"%12"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%38"⟩;Code.part25;dropfelt ⟨"%10"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%44"⟩;Code.part26;dropfelt ⟨"%9"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%47"⟩;Code.part27;dropfelt ⟨"%8"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%50"⟩;Code.part28;dropfelt ⟨"%6"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%56"⟩;Code.part29;dropfelt ⟨"%5"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%59"⟩;Code.part30;dropfelt ⟨"%4"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%62"⟩;Code.part31;dropfelt ⟨"%2"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%68"⟩;Code.part32;dropfelt ⟨"%1"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%71"⟩;Code.part33;dropfelt ⟨"%20"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;Code.part34;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩⟧

-- Prove that substituting part0_state for Code.part0 produces the same result
lemma part0_wp {st : State} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 data18 data19 : Option Felt} :
  Code.getReturn (Γ st ⟦Code.part0;dropfelt ⟨"%138"⟩;Code.part1;dropfelt ⟨"%139"⟩;dropfelt ⟨"%140"⟩;Code.part2;dropfelt ⟨"%141"⟩;dropfelt ⟨"%142"⟩;Code.part3;dropfelt ⟨"%143"⟩;dropfelt ⟨"%144"⟩;Code.part4;dropfelt ⟨"%145"⟩;dropfelt ⟨"%146"⟩;Code.part5;dropfelt ⟨"%147"⟩;dropfelt ⟨"%148"⟩;Code.part6;dropfelt ⟨"%149"⟩;dropfelt ⟨"%150"⟩;Code.part7;dropfelt ⟨"%151"⟩;dropfelt ⟨"%152"⟩;Code.part8;dropfelt ⟨"%153"⟩;dropfelt ⟨"%154"⟩;Code.part9;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;Code.part10;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;Code.part11;dropfelt ⟨"%159"⟩;dropfelt ⟨"%160"⟩;Code.part12;dropfelt ⟨"%161"⟩;dropfelt ⟨"%162"⟩;Code.part13;dropfelt ⟨"%163"⟩;dropfelt ⟨"%164"⟩;Code.part14;dropfelt ⟨"%165"⟩;dropfelt ⟨"%166"⟩;Code.part15;dropfelt ⟨"%167"⟩;dropfelt ⟨"%168"⟩;Code.part16;dropfelt ⟨"%169"⟩;dropfelt ⟨"%170"⟩;Code.part17;dropfelt ⟨"%171"⟩;dropfelt ⟨"%172"⟩;Code.part18;dropfelt ⟨"%173"⟩;dropfelt ⟨"%174"⟩;Code.part19;dropfelt ⟨"%175"⟩;dropfelt ⟨"%176"⟩;Code.part20;dropfelt ⟨"%17"⟩;dropfelt ⟨"%23"⟩;Code.part21;dropfelt ⟨"%16"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%26"⟩;Code.part22;dropfelt ⟨"%14"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%32"⟩;Code.part23;dropfelt ⟨"%13"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%35"⟩;Code.part24;dropfelt ⟨"%12"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%38"⟩;Code.part25;dropfelt ⟨"%10"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%44"⟩;Code.part26;dropfelt ⟨"%9"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%47"⟩;Code.part27;dropfelt ⟨"%8"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%50"⟩;Code.part28;dropfelt ⟨"%6"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%56"⟩;Code.part29;dropfelt ⟨"%5"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%59"⟩;Code.part30;dropfelt ⟨"%4"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%62"⟩;Code.part31;dropfelt ⟨"%2"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%68"⟩;Code.part32;dropfelt ⟨"%1"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%71"⟩;Code.part33;dropfelt ⟨"%20"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;Code.part34;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩⟧) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) ↔
  Code.getReturn (part0_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) := by
  generalize eq : (dropfelt ⟨"%138"⟩;Code.part1;dropfelt ⟨"%139"⟩;dropfelt ⟨"%140"⟩;Code.part2;dropfelt ⟨"%141"⟩;dropfelt ⟨"%142"⟩;Code.part3;dropfelt ⟨"%143"⟩;dropfelt ⟨"%144"⟩;Code.part4;dropfelt ⟨"%145"⟩;dropfelt ⟨"%146"⟩;Code.part5;dropfelt ⟨"%147"⟩;dropfelt ⟨"%148"⟩;Code.part6;dropfelt ⟨"%149"⟩;dropfelt ⟨"%150"⟩;Code.part7;dropfelt ⟨"%151"⟩;dropfelt ⟨"%152"⟩;Code.part8;dropfelt ⟨"%153"⟩;dropfelt ⟨"%154"⟩;Code.part9;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;Code.part10;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;Code.part11;dropfelt ⟨"%159"⟩;dropfelt ⟨"%160"⟩;Code.part12;dropfelt ⟨"%161"⟩;dropfelt ⟨"%162"⟩;Code.part13;dropfelt ⟨"%163"⟩;dropfelt ⟨"%164"⟩;Code.part14;dropfelt ⟨"%165"⟩;dropfelt ⟨"%166"⟩;Code.part15;dropfelt ⟨"%167"⟩;dropfelt ⟨"%168"⟩;Code.part16;dropfelt ⟨"%169"⟩;dropfelt ⟨"%170"⟩;Code.part17;dropfelt ⟨"%171"⟩;dropfelt ⟨"%172"⟩;Code.part18;dropfelt ⟨"%173"⟩;dropfelt ⟨"%174"⟩;Code.part19;dropfelt ⟨"%175"⟩;dropfelt ⟨"%176"⟩;Code.part20;dropfelt ⟨"%17"⟩;dropfelt ⟨"%23"⟩;Code.part21;dropfelt ⟨"%16"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%26"⟩;Code.part22;dropfelt ⟨"%14"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%32"⟩;Code.part23;dropfelt ⟨"%13"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%35"⟩;Code.part24;dropfelt ⟨"%12"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%38"⟩;Code.part25;dropfelt ⟨"%10"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%44"⟩;Code.part26;dropfelt ⟨"%9"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%47"⟩;Code.part27;dropfelt ⟨"%8"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%50"⟩;Code.part28;dropfelt ⟨"%6"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%56"⟩;Code.part29;dropfelt ⟨"%5"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%59"⟩;Code.part30;dropfelt ⟨"%4"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%62"⟩;Code.part31;dropfelt ⟨"%2"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%68"⟩;Code.part32;dropfelt ⟨"%1"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%71"⟩;Code.part33;dropfelt ⟨"%20"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;Code.part34;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) = prog
  unfold Code.part0
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part0_state_update part0_drops part0_state
  rfl

lemma part0_cumulative_wp {code0: Felt} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 data18 data19: Option Felt} :
  Code.run (start_state ([code0])) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) ↔
  Code.getReturn
      (part0_state_update
        {
          buffers :=
            Map.fromList
              [({ name := "code" : BufferVar }, [[some code0]]),
                ({ name := "data" : BufferVar },
                  [[none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none,
                      none, none, none, none]])],
          bufferWidths :=
            Map.fromList [({ name := "code" : BufferVar }, (1 : ℕ)), ({ name := "data" : BufferVar }, (20 : ℕ))],
          cycle := (0 : ℕ), felts := Map.empty, isFailed := false = true, props := Map.empty,
          vars := [{ name := "code" : BufferVar }, { name := "data" : BufferVar }] })
      ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14,
        data15, data16, data17, data18, data19])  := by
    unfold Code.run start_state
    rewrite [Code.optimised_behaviour_full]
    unfold MLIR.runProgram
    rewrite [←Code.parts_combine]
    unfold Code.parts_combined
    rewrite [←Code.getReturn_ignores_drops]
    rewrite [←Code.behaviour_with_drops]
    rewrite [part0_wp]
    rfl

end Risc0.OneHot20.Witness.WP