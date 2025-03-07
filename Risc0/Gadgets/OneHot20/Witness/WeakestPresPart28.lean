import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart27

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part28 on st
def part28_state (st: State) : State :=
  
        ((((st[felts][{ name := "%54" : FeltVar }] ←
                Option.get! (State.felts st { name := "%51" : FeltVar }) +
                  Option.get! (State.felts st { name := "%53" : FeltVar }))["%55"] ←ₛ
              getImpl st { name := "data" : BufferVar } (0 : Back) (13 : ℕ))[felts][{ name := "%56" : FeltVar }] ←
            Option.get!
                (State.felts
                  ((st[felts][{ name := "%54" : FeltVar }] ←
                      Option.get! (State.felts st { name := "%51" : FeltVar }) +
                        Option.get! (State.felts st { name := "%53" : FeltVar }))["%55"] ←ₛ
                    getImpl st { name := "data" : BufferVar } (0 : Back) (13 : ℕ))
                  { name := "%55" : FeltVar }) *
              Option.get! (State.felts st { name := "%6" : FeltVar }))[felts][{ name := "%57" : FeltVar }] ←
          Option.get! (State.felts st { name := "%51" : FeltVar }) +
              Option.get! (State.felts st { name := "%53" : FeltVar }) +
            Option.get!
                (State.felts
                  ((st[felts][{ name := "%54" : FeltVar }] ←
                      Option.get! (State.felts st { name := "%51" : FeltVar }) +
                        Option.get! (State.felts st { name := "%53" : FeltVar }))["%55"] ←ₛ
                    getImpl st { name := "data" : BufferVar } (0 : Back) (13 : ℕ))
                  { name := "%55" : FeltVar }) *
              Option.get! (State.felts st { name := "%6" : FeltVar })) 

def part28_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%6"⟩) ⟨"%51"⟩) ⟨"%53"⟩) ⟨"%54"⟩) ⟨"%56"⟩

-- Run the program from part28 onwards by using part28_state rather than Code.part28
def part28_state_update (st: State): State :=
  Γ (part28_drops (part28_state st)) ⟦Code.part29;dropfelt ⟨"%5"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%59"⟩;Code.part30;dropfelt ⟨"%4"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%62"⟩;Code.part31;dropfelt ⟨"%2"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%68"⟩;Code.part32;dropfelt ⟨"%1"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%71"⟩;Code.part33;dropfelt ⟨"%20"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;Code.part34;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩⟧

-- Prove that substituting part28_state for Code.part28 produces the same result
lemma part28_wp {st : State} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 data18 data19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part28;dropfelt ⟨"%6"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%56"⟩;Code.part29;dropfelt ⟨"%5"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%59"⟩;Code.part30;dropfelt ⟨"%4"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%62"⟩;Code.part31;dropfelt ⟨"%2"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%68"⟩;Code.part32;dropfelt ⟨"%1"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%71"⟩;Code.part33;dropfelt ⟨"%20"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;Code.part34;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) ↔
  Code.getReturn (part28_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%6"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%56"⟩;Code.part29;dropfelt ⟨"%5"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%59"⟩;Code.part30;dropfelt ⟨"%4"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%62"⟩;Code.part31;dropfelt ⟨"%2"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%68"⟩;Code.part32;dropfelt ⟨"%1"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%71"⟩;Code.part33;dropfelt ⟨"%20"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;Code.part34;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) = prog
  unfold Code.part28
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part28_state_update part28_drops part28_state
  rfl

lemma part28_updates_opaque {st : State} : 
  Code.getReturn (part27_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) ↔
  Code.getReturn (part28_state_update (part27_drops (part27_state st))) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) := by
  simp [part27_state_update, part28_wp]

lemma part28_cumulative_wp {code0: Felt} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 data18 data19: Option Felt} :
  Code.run (start_state ([code0])) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) ↔
  Code.getReturn
      (part28_state_update
        (((((((((((((({
                                      buffers :=
                                        ((fun x => Map.empty x)[{ name := "code" : BufferVar }] ←ₘ
                                            [[some code0]])[{ name := "data" : BufferVar }] ←ₘ
                                          [[some (if code0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some (if code0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some (if code0 - (2 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some (if code0 - (3 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some (if code0 - (4 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some (if code0 - (5 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some (if code0 - (6 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some (if code0 - (7 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some (if code0 - (8 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some (if code0 - (9 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some
                                                (if code0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some
                                                (if code0 - (11 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some
                                                (if code0 - (12 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some
                                                (if code0 - (13 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some
                                                (if code0 - (14 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some
                                                (if code0 - (15 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some
                                                (if code0 - (16 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some
                                                (if code0 - (17 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some
                                                (if code0 - (18 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some
                                                (if code0 - (19 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))]],
                                      bufferWidths :=
                                        ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                            (20 : ℕ))[{ name := "code" : BufferVar }] ←ₘ
                                          (1 : ℕ),
                                      cycle := (0 : ℕ),
                                      felts :=
                                        ((((((((Map.empty[{ name := "%20" : FeltVar }] ←ₘ
                                                          code0)[{ name := "%18" : FeltVar }] ←ₘ
                                                        (1 : Felt))[{ name := "%6" : FeltVar }] ←ₘ
                                                      (13 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                                    (14 : Felt))[{ name := "%4" : FeltVar }] ←ₘ
                                                  (15 : Felt))[{ name := "%3" : FeltVar }] ←ₘ
                                                (16 : Felt))[{ name := "%2" : FeltVar }] ←ₘ
                                              (17 : Felt))[{ name := "%1" : FeltVar }] ←ₘ
                                            (18 : Felt))[{ name := "%0" : FeltVar }] ←ₘ
                                          (19 : Felt),
                                      isFailed := False, props := Map.empty,
                                      vars :=
                                        [{ name := "code" : BufferVar },
                                          { name := "data" : BufferVar }] }[felts][{ name := "%22" : FeltVar }] ←
                                    if code0 - (2 : Felt) = (0 : Felt) then (1 : Felt)
                                    else (0 : Felt))[felts][{ name := "%21" : FeltVar }] ←
                                  if code0 - (1 : Felt) = (0 : Felt) then (1 : Felt)
                                  else (0 : Felt))[felts][{ name := "%25" : FeltVar }] ←
                                if code0 - (3 : Felt) = (0 : Felt) then (1 : Felt)
                                else (0 : Felt))[felts][{ name := "%28" : FeltVar }] ←
                              if code0 - (4 : Felt) = (0 : Felt) then (1 : Felt)
                              else (0 : Felt))[felts][{ name := "%31" : FeltVar }] ←
                            if code0 - (5 : Felt) = (0 : Felt) then (1 : Felt)
                            else (0 : Felt))[felts][{ name := "%34" : FeltVar }] ←
                          if code0 - (6 : Felt) = (0 : Felt) then (1 : Felt)
                          else (0 : Felt))[felts][{ name := "%37" : FeltVar }] ←
                        if code0 - (7 : Felt) = (0 : Felt) then (1 : Felt)
                        else (0 : Felt))[felts][{ name := "%40" : FeltVar }] ←
                      if code0 - (8 : Felt) = (0 : Felt) then (1 : Felt)
                      else (0 : Felt))[felts][{ name := "%43" : FeltVar }] ←
                    if code0 - (9 : Felt) = (0 : Felt) then (1 : Felt)
                    else (0 : Felt))[felts][{ name := "%46" : FeltVar }] ←
                  if code0 - (10 : Felt) = (0 : Felt) then (1 : Felt)
                  else (0 : Felt))[felts][{ name := "%49" : FeltVar }] ←
                if code0 - (11 : Felt) = (0 : Felt) then (1 : Felt)
                else (0 : Felt))[felts][{ name := "%51" : FeltVar }] ←
              (if code0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                  (if code0 - (2 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (2 : Felt) +
                                (if code0 - (3 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (3 : Felt) +
                              (if code0 - (4 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (4 : Felt) +
                            (if code0 - (5 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (5 : Felt) +
                          (if code0 - (6 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (6 : Felt) +
                        (if code0 - (7 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (7 : Felt) +
                      (if code0 - (8 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (8 : Felt) +
                    (if code0 - (9 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (9 : Felt) +
                  (if code0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (10 : Felt) +
                (if code0 - (11 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) *
                  (11 : Felt))[felts][{ name := "%52" : FeltVar }] ←
            if code0 - (12 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))[felts][{ name := "%53" : FeltVar }] ←
          (if code0 - (12 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (12 : Felt)))
      ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14,
        data15, data16, data17, data18, data19])  := by
    rewrite [part27_cumulative_wp]
    rewrite [part28_updates_opaque]
    unfold part27_state
    try simplify_get_hack
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part27_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.OneHot20.Witness.WP