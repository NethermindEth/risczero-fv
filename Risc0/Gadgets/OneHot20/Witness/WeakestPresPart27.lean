import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart26

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part27 on st
def part27_state (st: State) : State :=
  
          ((((st[felts][{ name := "%50" : FeltVar }] ←
                  Option.get! (State.felts st { name := "%49" : FeltVar }) *
                    Option.get! (State.felts st { name := "%8" : FeltVar }))[felts][{ name := "%51" : FeltVar }] ←
                Option.get! (State.felts st { name := "%48" : FeltVar }) +
                  Option.get! (State.felts st { name := "%49" : FeltVar }) *
                    Option.get! (State.felts st { name := "%8" : FeltVar }))["%52"] ←ₛ
              getImpl st { name := "data" : BufferVar } (0 : Back) (12 : ℕ))[felts][{ name := "%53" : FeltVar }] ←
            Option.get!
                (State.felts
                  (((st[felts][{ name := "%50" : FeltVar }] ←
                        Option.get! (State.felts st { name := "%49" : FeltVar }) *
                          Option.get! (State.felts st { name := "%8" : FeltVar }))[felts][{ name := "%51" : FeltVar }] ←
                      Option.get! (State.felts st { name := "%48" : FeltVar }) +
                        Option.get! (State.felts st { name := "%49" : FeltVar }) *
                          Option.get! (State.felts st { name := "%8" : FeltVar }))["%52"] ←ₛ
                    getImpl st { name := "data" : BufferVar } (0 : Back) (12 : ℕ))
                  { name := "%52" : FeltVar }) *
              Option.get! (State.felts st { name := "%7" : FeltVar })) 

def part27_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%8"⟩) ⟨"%7"⟩) ⟨"%48"⟩) ⟨"%50"⟩

-- Run the program from part27 onwards by using part27_state rather than Code.part27
def part27_state_update (st: State): State :=
  Γ (part27_drops (part27_state st)) ⟦Code.part28;dropfelt ⟨"%6"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%56"⟩;Code.part29;dropfelt ⟨"%5"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%59"⟩;Code.part30;dropfelt ⟨"%4"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%62"⟩;Code.part31;dropfelt ⟨"%2"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%68"⟩;Code.part32;dropfelt ⟨"%1"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%71"⟩;Code.part33;dropfelt ⟨"%20"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;Code.part34;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩⟧

-- Prove that substituting part27_state for Code.part27 produces the same result
lemma part27_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part27;dropfelt ⟨"%8"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%50"⟩;Code.part28;dropfelt ⟨"%6"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%56"⟩;Code.part29;dropfelt ⟨"%5"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%59"⟩;Code.part30;dropfelt ⟨"%4"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%62"⟩;Code.part31;dropfelt ⟨"%2"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%68"⟩;Code.part32;dropfelt ⟨"%1"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%71"⟩;Code.part33;dropfelt ⟨"%20"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;Code.part34;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part27_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%8"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%50"⟩;Code.part28;dropfelt ⟨"%6"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%56"⟩;Code.part29;dropfelt ⟨"%5"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%59"⟩;Code.part30;dropfelt ⟨"%4"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%62"⟩;Code.part31;dropfelt ⟨"%2"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%68"⟩;Code.part32;dropfelt ⟨"%1"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%71"⟩;Code.part33;dropfelt ⟨"%20"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;Code.part34;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) = prog
  unfold Code.part27
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part27_state_update part27_drops part27_state
  rfl

lemma part27_updates_opaque {st : State} : 
  Code.getReturn (part26_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part27_state_update (part26_drops (part26_state st))) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part26_state_update, part27_wp]

lemma part27_cumulative_wp {x0: Felt} :
  Code.run (start_state [x0]) = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19] ↔
  Code.getReturn
        (part27_state_update
          (((((((((((({
                                    buffers :=
                                      ((fun x => Map.empty x)[{ name := "code" : BufferVar }] ←ₘ
                                          [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                        [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                            some (if x0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                            some (if x0 - (2 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                            some (if x0 - (3 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                            some (if x0 - (4 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                            some (if x0 - (5 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                            some (if x0 - (6 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                            some (if x0 - (7 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                            some (if x0 - (8 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                            some (if x0 - (9 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                            some (if x0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                            some (if x0 - (11 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                            some (if x0 - (12 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                            some (if x0 - (13 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                            some (if x0 - (14 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                            some (if x0 - (15 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                            some (if x0 - (16 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                            some (if x0 - (17 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                            some (if x0 - (18 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                            some (if x0 - (19 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))]],
                                    bufferWidths :=
                                      ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                          (20 : ℕ))[{ name := "code" : BufferVar }] ←ₘ
                                        (1 : ℕ),
                                    constraints := [], cycle := (0 : ℕ),
                                    felts :=
                                      ((((((((((Map.empty[{ name := "%20" : FeltVar }] ←ₘ
                                                            x0)[{ name := "%18" : FeltVar }] ←ₘ
                                                          (1 : Felt))[{ name := "%8" : FeltVar }] ←ₘ
                                                        (11 : Felt))[{ name := "%7" : FeltVar }] ←ₘ
                                                      (12 : Felt))[{ name := "%6" : FeltVar }] ←ₘ
                                                    (13 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                                  (14 : Felt))[{ name := "%4" : FeltVar }] ←ₘ
                                                (15 : Felt))[{ name := "%3" : FeltVar }] ←ₘ
                                              (16 : Felt))[{ name := "%2" : FeltVar }] ←ₘ
                                            (17 : Felt))[{ name := "%1" : FeltVar }] ←ₘ
                                          (18 : Felt))[{ name := "%0" : FeltVar }] ←ₘ
                                        (19 : Felt),
                                    isFailed := false, props := Map.empty,
                                    vars :=
                                      [{ name := "code" : BufferVar },
                                        { name := "data" : BufferVar }] }[felts][{ name := "%22" : FeltVar }] ←
                                  if x0 - (2 : Felt) = (0 : Felt) then (1 : Felt)
                                  else (0 : Felt))[felts][{ name := "%21" : FeltVar }] ←
                                if x0 - (1 : Felt) = (0 : Felt) then (1 : Felt)
                                else (0 : Felt))[felts][{ name := "%25" : FeltVar }] ←
                              if x0 - (3 : Felt) = (0 : Felt) then (1 : Felt)
                              else (0 : Felt))[felts][{ name := "%28" : FeltVar }] ←
                            if x0 - (4 : Felt) = (0 : Felt) then (1 : Felt)
                            else (0 : Felt))[felts][{ name := "%31" : FeltVar }] ←
                          if x0 - (5 : Felt) = (0 : Felt) then (1 : Felt)
                          else (0 : Felt))[felts][{ name := "%34" : FeltVar }] ←
                        if x0 - (6 : Felt) = (0 : Felt) then (1 : Felt)
                        else (0 : Felt))[felts][{ name := "%37" : FeltVar }] ←
                      if x0 - (7 : Felt) = (0 : Felt) then (1 : Felt)
                      else (0 : Felt))[felts][{ name := "%40" : FeltVar }] ←
                    if x0 - (8 : Felt) = (0 : Felt) then (1 : Felt)
                    else (0 : Felt))[felts][{ name := "%43" : FeltVar }] ←
                  if x0 - (9 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))[felts][{ name := "%46" : FeltVar }] ←
                if x0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))[felts][{ name := "%48" : FeltVar }] ←
              (if x0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                (if x0 - (2 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (2 : Felt) +
                              (if x0 - (3 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (3 : Felt) +
                            (if x0 - (4 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (4 : Felt) +
                          (if x0 - (5 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (5 : Felt) +
                        (if x0 - (6 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (6 : Felt) +
                      (if x0 - (7 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (7 : Felt) +
                    (if x0 - (8 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (8 : Felt) +
                  (if x0 - (9 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (9 : Felt) +
                (if x0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) *
                  (10 : Felt))[felts][{ name := "%49" : FeltVar }] ←
            if x0 - (11 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))) =
      [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19]  := by
    rewrite [part26_cumulative_wp]
    rewrite [part27_updates_opaque]
    unfold part26_state
    try simplify_get_hack
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part26_drops
    -- 3 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.constraints_if_eq_if_constraints,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.OneHot20.Witness.WP