import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart33

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part34 on st
def part34_state (st: State) : State :=
  
          (withEqZero
            (Option.get! (State.felts (st["%77"] ←ₛ getImpl st { name := "data" } 0 0) { name := "%77" }) *
              (Option.get! (State.felts st { name := "%18" }) -
                Option.get! (State.felts (st["%77"] ←ₛ getImpl st { name := "data" } 0 0) { name := "%77" })))
            (((st["%77"] ←ₛ getImpl st { name := "data" } 0 0)[felts][{ name := "%78" }] ←
                Option.get! (State.felts st { name := "%18" }) -
                  Option.get!
                    (State.felts (st["%77"] ←ₛ getImpl st { name := "data" } 0 0)
                      { name := "%77" }))[felts][{ name := "%79" }] ←
              Option.get! (State.felts (st["%77"] ←ₛ getImpl st { name := "data" } 0 0) { name := "%77" }) *
                (Option.get! (State.felts st { name := "%18" }) -
                  Option.get!
                    (State.felts (st["%77"] ←ₛ getImpl st { name := "data" } 0 0) { name := "%77" })))) 

def part34_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (st) ⟨"%78"⟩) ⟨"%79"⟩

-- Run the program from part34 onwards by using part34_state rather than Code.part34
def part34_state_update (st: State): State :=
  Γ (part34_drops (part34_state st)) ⟦Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩⟧

-- Prove that substituting part34_state for Code.part34 produces the same result
lemma part34_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part34;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part34_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;Code.part35;dropfelt ⟨"%21"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%81"⟩;Code.part36;dropfelt ⟨"%22"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%84"⟩;Code.part37;dropfelt ⟨"%25"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;Code.part38;dropfelt ⟨"%28"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;Code.part39;dropfelt ⟨"%31"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;Code.part40;dropfelt ⟨"%34"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;Code.part41;dropfelt ⟨"%37"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part42;dropfelt ⟨"%40"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%102"⟩;Code.part43;dropfelt ⟨"%43"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%105"⟩;Code.part44;dropfelt ⟨"%46"⟩;dropfelt ⟨"%106"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%108"⟩;Code.part45;dropfelt ⟨"%49"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%110"⟩;dropfelt ⟨"%111"⟩;Code.part46;dropfelt ⟨"%52"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%114"⟩;Code.part47;dropfelt ⟨"%55"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%117"⟩;Code.part48;dropfelt ⟨"%58"⟩;dropfelt ⟨"%118"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%120"⟩;Code.part49;dropfelt ⟨"%61"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%122"⟩;dropfelt ⟨"%123"⟩;Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) = prog
  unfold Code.part34
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part34_state_update part34_drops part34_state
  rfl

lemma part34_updates_opaque {st : State} : 
  Code.getReturn (part33_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part34_state_update (part33_drops (part33_state st))) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part33_state_update, part34_wp]

lemma part34_cumulative_wp {x0: Felt} :
  Code.run (start_state [x0]) = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19] ↔
  Code.getReturn
        (part34_state_update
          {
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
            constraints :=
              [(if x0 - 1 = 0 then 1 else 0) + (if x0 - 2 = 0 then 1 else 0) * 2 + (if x0 - 3 = 0 then 1 else 0) * 3 +
                                                    (if x0 - 4 = 0 then 1 else 0) * 4 +
                                                  (if x0 - 5 = 0 then 1 else 0) * 5 +
                                                (if x0 - 6 = 0 then 1 else 0) * 6 +
                                              (if x0 - 7 = 0 then 1 else 0) * 7 +
                                            (if x0 - 8 = 0 then 1 else 0) * 8 +
                                          (if x0 - 9 = 0 then 1 else 0) * 9 +
                                        (if x0 - 10 = 0 then 1 else 0) * 10 +
                                      (if x0 - 11 = 0 then 1 else 0) * 11 +
                                    (if x0 - 12 = 0 then 1 else 0) * 12 +
                                  (if x0 - 13 = 0 then 1 else 0) * 13 +
                                (if x0 - 14 = 0 then 1 else 0) * 14 +
                              (if x0 - 15 = 0 then 1 else 0) * 15 +
                            (if x0 - 16 = 0 then 1 else 0) * 16 +
                          (if x0 - 17 = 0 then 1 else 0) * 17 +
                        (if x0 - 18 = 0 then 1 else 0) * 18 +
                      (if x0 - 19 = 0 then 1 else 0) * 19 -
                    x0 =
                  0],
            cycle := 0,
            felts :=
              (((((((((((((((((((Map.empty[{ name := "%18" }] ←ₘ 1)[{ name := "%22" }] ←ₘ
                                                    if x0 - 2 = 0 then 1 else 0)[{ name := "%21" }] ←ₘ
                                                  if x0 - 1 = 0 then 1 else 0)[{ name := "%25" }] ←ₘ
                                                if x0 - 3 = 0 then 1 else 0)[{ name := "%28" }] ←ₘ
                                              if x0 - 4 = 0 then 1 else 0)[{ name := "%31" }] ←ₘ
                                            if x0 - 5 = 0 then 1 else 0)[{ name := "%34" }] ←ₘ
                                          if x0 - 6 = 0 then 1 else 0)[{ name := "%37" }] ←ₘ
                                        if x0 - 7 = 0 then 1 else 0)[{ name := "%40" }] ←ₘ
                                      if x0 - 8 = 0 then 1 else 0)[{ name := "%43" }] ←ₘ
                                    if x0 - 9 = 0 then 1 else 0)[{ name := "%46" }] ←ₘ
                                  if x0 - 10 = 0 then 1 else 0)[{ name := "%49" }] ←ₘ
                                if x0 - 11 = 0 then 1 else 0)[{ name := "%52" }] ←ₘ
                              if x0 - 12 = 0 then 1 else 0)[{ name := "%55" }] ←ₘ
                            if x0 - 13 = 0 then 1 else 0)[{ name := "%58" }] ←ₘ
                          if x0 - 14 = 0 then 1 else 0)[{ name := "%61" }] ←ₘ
                        if x0 - 15 = 0 then 1 else 0)[{ name := "%64" }] ←ₘ
                      if x0 - 16 = 0 then 1 else 0)[{ name := "%67" }] ←ₘ
                    if x0 - 17 = 0 then 1 else 0)[{ name := "%70" }] ←ₘ
                  if x0 - 18 = 0 then 1 else 0)[{ name := "%73" }] ←ₘ
                if x0 - 19 = 0 then 1 else 0,
            isFailed := false, props := Map.empty, vars := [{ name := "code" }, { name := "data" }] }) =
      [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19]  := by
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
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

end Risc0.OneHot20.Witness.WP