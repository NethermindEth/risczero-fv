import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart22

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part23 on st
def part23_state (st: State) : State :=
  
          ((((st["%34"] ←ₛ getImpl st { name := "data" } 0 6)[felts][{ name := "%35" }] ←
                Option.get! (State.felts (st["%34"] ←ₛ getImpl st { name := "data" } 0 6) { name := "%34" }) *
                  Option.get! (State.felts st { name := "%13" }))[felts][{ name := "%36" }] ←
              Option.get! (State.felts st { name := "%33" }) +
                Option.get! (State.felts (st["%34"] ←ₛ getImpl st { name := "data" } 0 6) { name := "%34" }) *
                  Option.get! (State.felts st { name := "%13" }))["%37"] ←ₛ
            getImpl st { name := "data" } 0 7) 

def part23_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%13"⟩) ⟨"%33"⟩) ⟨"%35"⟩

-- Run the program from part23 onwards by using part23_state rather than Code.part23
def part23_state_update (st: State): State :=
  Γ (part23_drops (part23_state st)) ⟦Code.part24;dropfelt ⟨"%12"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%38"⟩;Code.part25;dropfelt ⟨"%10"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%44"⟩;Code.part26;dropfelt ⟨"%9"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%47"⟩;Code.part27;dropfelt ⟨"%8"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%50"⟩;Code.part28;dropfelt ⟨"%6"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%56"⟩;Code.part29;dropfelt ⟨"%5"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%59"⟩;Code.part30;dropfelt ⟨"%4"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%62"⟩;Code.part31;dropfelt ⟨"%2"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%68"⟩;Code.part32;dropfelt ⟨"%1"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%71"⟩;Code.part33;dropfelt ⟨"%20"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;Code.part34;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩⟧

-- Prove that substituting part23_state for Code.part23 produces the same result
lemma part23_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part23;dropfelt ⟨"%13"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%35"⟩;Code.part24;dropfelt ⟨"%12"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%38"⟩;Code.part25;dropfelt ⟨"%10"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%44"⟩;Code.part26;dropfelt ⟨"%9"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%47"⟩;Code.part27;dropfelt ⟨"%8"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%50"⟩;Code.part28;dropfelt ⟨"%6"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%56"⟩;Code.part29;dropfelt ⟨"%5"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%59"⟩;Code.part30;dropfelt ⟨"%4"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%62"⟩;Code.part31;dropfelt ⟨"%2"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%68"⟩;Code.part32;dropfelt ⟨"%1"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%71"⟩;Code.part33;dropfelt ⟨"%20"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;Code.part34;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part23_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%13"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%35"⟩;Code.part24;dropfelt ⟨"%12"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%38"⟩;Code.part25;dropfelt ⟨"%10"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%44"⟩;Code.part26;dropfelt ⟨"%9"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%47"⟩;Code.part27;dropfelt ⟨"%8"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%50"⟩;Code.part28;dropfelt ⟨"%6"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%56"⟩;Code.part29;dropfelt ⟨"%5"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%59"⟩;Code.part30;dropfelt ⟨"%4"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%62"⟩;Code.part31;dropfelt ⟨"%2"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%68"⟩;Code.part32;dropfelt ⟨"%1"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%71"⟩;Code.part33;dropfelt ⟨"%20"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;Code.part34;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) = prog
  unfold Code.part23
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part23_state_update part23_drops part23_state
  rfl

lemma part23_updates_opaque {st : State} : 
  Code.getReturn (part22_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part23_state_update (part22_drops (part22_state st))) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part22_state_update, part23_wp]

lemma part23_cumulative_wp {x0: Felt} :
  Code.run (start_state [x0]) = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19] ↔
  Code.getReturn
        (part23_state_update
          (((((({
                        buffers :=
                          ((fun x => Map.empty x)[{ name := "code" }] ←ₘ [[some x0]])[{ name := "data" }] ←ₘ
                            [[some (if x0 = 0 then 1 else 0), some (if x0 - 1 = 0 then 1 else 0),
                                some (if x0 - 2 = 0 then 1 else 0), some (if x0 - 3 = 0 then 1 else 0),
                                some (if x0 - 4 = 0 then 1 else 0), some (if x0 - 5 = 0 then 1 else 0),
                                some (if x0 - 6 = 0 then 1 else 0), some (if x0 - 7 = 0 then 1 else 0),
                                some (if x0 - 8 = 0 then 1 else 0), some (if x0 - 9 = 0 then 1 else 0),
                                some (if x0 - 10 = 0 then 1 else 0), some (if x0 - 11 = 0 then 1 else 0),
                                some (if x0 - 12 = 0 then 1 else 0), some (if x0 - 13 = 0 then 1 else 0),
                                some (if x0 - 14 = 0 then 1 else 0), some (if x0 - 15 = 0 then 1 else 0),
                                some (if x0 - 16 = 0 then 1 else 0), some (if x0 - 17 = 0 then 1 else 0),
                                some (if x0 - 18 = 0 then 1 else 0), some (if x0 - 19 = 0 then 1 else 0)]],
                        bufferWidths := ((fun x => Map.empty x)[{ name := "data" }] ←ₘ 20)[{ name := "code" }] ←ₘ 1,
                        constraints := [], cycle := 0,
                        felts :=
                          (((((((((((((((Map.empty[{ name := "%20" }] ←ₘ x0)[{ name := "%18" }] ←ₘ
                                                        1)[{ name := "%13" }] ←ₘ
                                                      6)[{ name := "%12" }] ←ₘ
                                                    7)[{ name := "%11" }] ←ₘ
                                                  8)[{ name := "%10" }] ←ₘ
                                                9)[{ name := "%9" }] ←ₘ
                                              10)[{ name := "%8" }] ←ₘ
                                            11)[{ name := "%7" }] ←ₘ
                                          12)[{ name := "%6" }] ←ₘ
                                        13)[{ name := "%5" }] ←ₘ
                                      14)[{ name := "%4" }] ←ₘ
                                    15)[{ name := "%3" }] ←ₘ
                                  16)[{ name := "%2" }] ←ₘ
                                17)[{ name := "%1" }] ←ₘ
                              18)[{ name := "%0" }] ←ₘ
                            19,
                        isFailed := false, props := Map.empty,
                        vars := [{ name := "code" }, { name := "data" }] }[felts][{ name := "%22" }] ←
                      if x0 - 2 = 0 then 1 else 0)[felts][{ name := "%21" }] ←
                    if x0 - 1 = 0 then 1 else 0)[felts][{ name := "%25" }] ←
                  if x0 - 3 = 0 then 1 else 0)[felts][{ name := "%28" }] ←
                if x0 - 4 = 0 then 1 else 0)[felts][{ name := "%31" }] ←
              if x0 - 5 = 0 then 1 else 0)[felts][{ name := "%33" }] ←
            (if x0 - 1 = 0 then 1 else 0) + (if x0 - 2 = 0 then 1 else 0) * 2 + (if x0 - 3 = 0 then 1 else 0) * 3 +
                (if x0 - 4 = 0 then 1 else 0) * 4 +
              (if x0 - 5 = 0 then 1 else 0) * 5)) =
      [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19]  := by
    rewrite [part22_cumulative_wp]
    rewrite [part23_updates_opaque]
    unfold part22_state
    try simplify_get_hack
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part22_drops
    -- 5 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

end Risc0.OneHot20.Witness.WP