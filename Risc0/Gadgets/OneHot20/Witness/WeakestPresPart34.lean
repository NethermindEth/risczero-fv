import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart33

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part34 on st
def part34_state (st: State) : State :=
  
        (withEqZero
          (((st["%77"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (0 : ℕ)).felts
                { name := "%77" : FeltVar }).get! *
            ((st.felts { name := "%18" : FeltVar }).get! -
              ((st["%77"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (0 : ℕ)).felts
                  { name := "%77" : FeltVar }).get!))
          (((st["%77"] ←ₛ
                getImpl st { name := "data" : BufferVar } (0 : Back) (0 : ℕ))[felts][{ name := "%78" : FeltVar }] ←
              (st.felts { name := "%18" : FeltVar }).get! -
                ((st["%77"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (0 : ℕ)).felts
                    { name := "%77" : FeltVar }).get!)[felts][{ name := "%79" : FeltVar }] ←
            ((st["%77"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (0 : ℕ)).felts
                  { name := "%77" : FeltVar }).get! *
              ((st.felts { name := "%18" : FeltVar }).get! -
                ((st["%77"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (0 : ℕ)).felts
                    { name := "%77" : FeltVar }).get!))) 

def part34_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (st) ⟨"%78"⟩) ⟨"%79"⟩

-- Run the program from part34 onwards by using part34_state rather than Code.part34
def part34_state_update (st: State): State :=
  Γ (part34_drops (part34_state st)) ⟦Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩⟧

-- Prove that substituting part34_state for Code.part34 produces the same result
lemma part34_wp {st : State} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 data18 data19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part34;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) ↔
  Code.getReturn (part34_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) := by
  unfold MLIR.runProgram; try simp only
  generalize eq : (dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) = prog
  unfold Code.part34
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part34_state_update part34_drops part34_state
  rfl

lemma part34_updates_opaque {st : State} : 
  Code.getReturn (part33_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) ↔
  Code.getReturn (part34_state_update (part33_drops (part33_state st))) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) := by
  try simp [part33_state_update, part34_wp]

lemma part34_cumulative_wp {code0: Felt} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 data18 data19: Option Felt} :
  Code.run (start_state ([code0])) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) ↔
  Code.getReturn
      (part34_state_update
        {
          buffers :=
            (Map.empty[{ name := "code" : BufferVar }] ←ₘ [[some code0]])[{ name := "data" : BufferVar }] ←ₘ
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
                  some (if code0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                  some (if code0 - (11 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                  some (if code0 - (12 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                  some (if code0 - (13 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                  some (if code0 - (14 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                  some (if code0 - (15 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                  some (if code0 - (16 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                  some (if code0 - (17 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                  some (if code0 - (18 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                  some (if code0 - (19 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))]],
          bufferWidths :=
            (Map.empty[{ name := "data" : BufferVar }] ←ₘ (20 : ℕ))[{ name := "code" : BufferVar }] ←ₘ (1 : ℕ),
          cycle := (0 : ℕ),
          felts :=
            (((((((((((((((((((Map.empty[{ name := "%18" : FeltVar }] ←ₘ (1 : Felt))[{ name := "%22" : FeltVar }] ←ₘ
                                                  if code0 - (2 : Felt) = (0 : Felt) then (1 : Felt)
                                                  else (0 : Felt))[{ name := "%21" : FeltVar }] ←ₘ
                                                if code0 - (1 : Felt) = (0 : Felt) then (1 : Felt)
                                                else (0 : Felt))[{ name := "%25" : FeltVar }] ←ₘ
                                              if code0 - (3 : Felt) = (0 : Felt) then (1 : Felt)
                                              else (0 : Felt))[{ name := "%28" : FeltVar }] ←ₘ
                                            if code0 - (4 : Felt) = (0 : Felt) then (1 : Felt)
                                            else (0 : Felt))[{ name := "%31" : FeltVar }] ←ₘ
                                          if code0 - (5 : Felt) = (0 : Felt) then (1 : Felt)
                                          else (0 : Felt))[{ name := "%34" : FeltVar }] ←ₘ
                                        if code0 - (6 : Felt) = (0 : Felt) then (1 : Felt)
                                        else (0 : Felt))[{ name := "%37" : FeltVar }] ←ₘ
                                      if code0 - (7 : Felt) = (0 : Felt) then (1 : Felt)
                                      else (0 : Felt))[{ name := "%40" : FeltVar }] ←ₘ
                                    if code0 - (8 : Felt) = (0 : Felt) then (1 : Felt)
                                    else (0 : Felt))[{ name := "%43" : FeltVar }] ←ₘ
                                  if code0 - (9 : Felt) = (0 : Felt) then (1 : Felt)
                                  else (0 : Felt))[{ name := "%46" : FeltVar }] ←ₘ
                                if code0 - (10 : Felt) = (0 : Felt) then (1 : Felt)
                                else (0 : Felt))[{ name := "%49" : FeltVar }] ←ₘ
                              if code0 - (11 : Felt) = (0 : Felt) then (1 : Felt)
                              else (0 : Felt))[{ name := "%52" : FeltVar }] ←ₘ
                            if code0 - (12 : Felt) = (0 : Felt) then (1 : Felt)
                            else (0 : Felt))[{ name := "%55" : FeltVar }] ←ₘ
                          if code0 - (13 : Felt) = (0 : Felt) then (1 : Felt)
                          else (0 : Felt))[{ name := "%58" : FeltVar }] ←ₘ
                        if code0 - (14 : Felt) = (0 : Felt) then (1 : Felt)
                        else (0 : Felt))[{ name := "%61" : FeltVar }] ←ₘ
                      if code0 - (15 : Felt) = (0 : Felt) then (1 : Felt)
                      else (0 : Felt))[{ name := "%64" : FeltVar }] ←ₘ
                    if code0 - (16 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))[{ name := "%67" : FeltVar }] ←ₘ
                  if code0 - (17 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))[{ name := "%70" : FeltVar }] ←ₘ
                if code0 - (18 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))[{ name := "%73" : FeltVar }] ←ₘ
              if code0 - (19 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt),
          isFailed :=
            ¬(((((((((((((((((((if code0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                                      if code0 - (2 : Felt) = (0 : Felt) then (2 : Felt)
                                                      else (0 : Felt)) +
                                                    if code0 - (3 : Felt) = (0 : Felt) then (3 : Felt)
                                                    else (0 : Felt)) +
                                                  if code0 - (4 : Felt) = (0 : Felt) then (4 : Felt) else (0 : Felt)) +
                                                if code0 - (5 : Felt) = (0 : Felt) then (5 : Felt) else (0 : Felt)) +
                                              if code0 - (6 : Felt) = (0 : Felt) then (6 : Felt) else (0 : Felt)) +
                                            if code0 - (7 : Felt) = (0 : Felt) then (7 : Felt) else (0 : Felt)) +
                                          if code0 - (8 : Felt) = (0 : Felt) then (8 : Felt) else (0 : Felt)) +
                                        if code0 - (9 : Felt) = (0 : Felt) then (9 : Felt) else (0 : Felt)) +
                                      if code0 - (10 : Felt) = (0 : Felt) then (10 : Felt) else (0 : Felt)) +
                                    if code0 - (11 : Felt) = (0 : Felt) then (11 : Felt) else (0 : Felt)) +
                                  if code0 - (12 : Felt) = (0 : Felt) then (12 : Felt) else (0 : Felt)) +
                                if code0 - (13 : Felt) = (0 : Felt) then (13 : Felt) else (0 : Felt)) +
                              if code0 - (14 : Felt) = (0 : Felt) then (14 : Felt) else (0 : Felt)) +
                            if code0 - (15 : Felt) = (0 : Felt) then (15 : Felt) else (0 : Felt)) +
                          if code0 - (16 : Felt) = (0 : Felt) then (16 : Felt) else (0 : Felt)) +
                        if code0 - (17 : Felt) = (0 : Felt) then (17 : Felt) else (0 : Felt)) +
                      if code0 - (18 : Felt) = (0 : Felt) then (18 : Felt) else (0 : Felt)) +
                    if code0 - (19 : Felt) = (0 : Felt) then (19 : Felt) else (0 : Felt)) -
                  code0 =
                (0 : Felt),
          props := Map.empty, vars := [{ name := "code" : BufferVar }, { name := "data" : BufferVar }] })
      ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14,
        data15, data16, data17, data18, data19])  := by
    rewrite [part33_cumulative_wp]
    rewrite [part34_updates_opaque]
    unfold part33_state
    try simplify_get_hack
    MLIR_states_updates
    -- 1 withEqZero
    rewrite [withEqZero_def]
    MLIR_states_updates
    unfold part33_drops
    -- 6 drops
    try simp [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    try simp [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    try simp [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- try simp [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.OneHot20.Witness.WP