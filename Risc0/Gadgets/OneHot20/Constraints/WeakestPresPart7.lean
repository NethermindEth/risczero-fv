import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart6

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part7 on st
def part7_state (st: State) : State :=
  
        ((((st[felts][{ name := "%41" : FeltVar }] ←
                Option.get! (State.felts st { name := "%40" : FeltVar }) *
                  Option.get! (State.felts st { name := "%7" : FeltVar }))[felts][{ name := "%42" : FeltVar }] ←
              Option.get! (State.felts st { name := "%39" : FeltVar }) +
                Option.get! (State.felts st { name := "%40" : FeltVar }) *
                  Option.get! (State.felts st { name := "%7" : FeltVar }))[felts][{ name := "%8" : FeltVar }] ←
            (9 : Felt))["%43"] ←ₛ
          getImpl st { name := "data" : BufferVar } (0 : Back) (9 : ℕ)) 

def part7_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%39"⟩) ⟨"%7"⟩) ⟨"%41"⟩

-- Run the program from part7 onwards by using part7_state rather than Code.part7
def part7_state_update (st: State): State :=
  Γ (part7_drops (part7_state st)) ⟦Code.part8;dropfelt ⟨"%42"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%44"⟩;Code.part9;dropfelt ⟨"%45"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%47"⟩;Code.part10;dropfelt ⟨"%48"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%50"⟩;Code.part11;dropfelt ⟨"%51"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%53"⟩;Code.part12;dropfelt ⟨"%54"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%56"⟩;Code.part13;dropfelt ⟨"%57"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%59"⟩;Code.part14;dropfelt ⟨"%60"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%62"⟩;Code.part15;dropfelt ⟨"%63"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%65"⟩;Code.part16;dropfelt ⟨"%66"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%68"⟩;Code.part17;dropfelt ⟨"%69"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%71"⟩;Code.part18;dropfelt ⟨"%72"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%20"⟩;Code.part19;dropfelt ⟨"%76"⟩;Code.part20;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%82"⟩;Code.part21;dropfelt ⟨"%21"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%86"⟩;Code.part22;dropfelt ⟨"%22"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%90"⟩;Code.part23;dropfelt ⟨"%25"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%94"⟩;Code.part24;dropfelt ⟨"%28"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%98"⟩;Code.part25;dropfelt ⟨"%31"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%102"⟩;Code.part26;dropfelt ⟨"%34"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%106"⟩;Code.part27;dropfelt ⟨"%37"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%110"⟩;Code.part28;dropfelt ⟨"%40"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%111"⟩;dropfelt ⟨"%114"⟩;Code.part29;dropfelt ⟨"%43"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%118"⟩;Code.part30;dropfelt ⟨"%46"⟩;dropfelt ⟨"%117"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%122"⟩;Code.part31;dropfelt ⟨"%49"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%123"⟩;dropfelt ⟨"%126"⟩;Code.part32;dropfelt ⟨"%52"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%130"⟩;Code.part33;dropfelt ⟨"%55"⟩;dropfelt ⟨"%129"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%134"⟩;Code.part34;dropfelt ⟨"%58"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%135"⟩;dropfelt ⟨"%138"⟩;Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%73"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩⟧

-- Prove that substituting part7_state for Code.part7 produces the same result
lemma part7_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part7;dropfelt ⟨"%39"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%41"⟩;Code.part8;dropfelt ⟨"%42"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%44"⟩;Code.part9;dropfelt ⟨"%45"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%47"⟩;Code.part10;dropfelt ⟨"%48"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%50"⟩;Code.part11;dropfelt ⟨"%51"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%53"⟩;Code.part12;dropfelt ⟨"%54"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%56"⟩;Code.part13;dropfelt ⟨"%57"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%59"⟩;Code.part14;dropfelt ⟨"%60"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%62"⟩;Code.part15;dropfelt ⟨"%63"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%65"⟩;Code.part16;dropfelt ⟨"%66"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%68"⟩;Code.part17;dropfelt ⟨"%69"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%71"⟩;Code.part18;dropfelt ⟨"%72"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%20"⟩;Code.part19;dropfelt ⟨"%76"⟩;Code.part20;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%82"⟩;Code.part21;dropfelt ⟨"%21"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%86"⟩;Code.part22;dropfelt ⟨"%22"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%90"⟩;Code.part23;dropfelt ⟨"%25"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%94"⟩;Code.part24;dropfelt ⟨"%28"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%98"⟩;Code.part25;dropfelt ⟨"%31"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%102"⟩;Code.part26;dropfelt ⟨"%34"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%106"⟩;Code.part27;dropfelt ⟨"%37"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%110"⟩;Code.part28;dropfelt ⟨"%40"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%111"⟩;dropfelt ⟨"%114"⟩;Code.part29;dropfelt ⟨"%43"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%118"⟩;Code.part30;dropfelt ⟨"%46"⟩;dropfelt ⟨"%117"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%122"⟩;Code.part31;dropfelt ⟨"%49"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%123"⟩;dropfelt ⟨"%126"⟩;Code.part32;dropfelt ⟨"%52"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%130"⟩;Code.part33;dropfelt ⟨"%55"⟩;dropfelt ⟨"%129"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%134"⟩;Code.part34;dropfelt ⟨"%58"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%135"⟩;dropfelt ⟨"%138"⟩;Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%73"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩) st) ↔
  Code.getReturn (part7_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%39"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%41"⟩;Code.part8;dropfelt ⟨"%42"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%44"⟩;Code.part9;dropfelt ⟨"%45"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%47"⟩;Code.part10;dropfelt ⟨"%48"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%50"⟩;Code.part11;dropfelt ⟨"%51"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%53"⟩;Code.part12;dropfelt ⟨"%54"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%56"⟩;Code.part13;dropfelt ⟨"%57"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%59"⟩;Code.part14;dropfelt ⟨"%60"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%62"⟩;Code.part15;dropfelt ⟨"%63"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%65"⟩;Code.part16;dropfelt ⟨"%66"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%68"⟩;Code.part17;dropfelt ⟨"%69"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%71"⟩;Code.part18;dropfelt ⟨"%72"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%20"⟩;Code.part19;dropfelt ⟨"%76"⟩;Code.part20;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%82"⟩;Code.part21;dropfelt ⟨"%21"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%86"⟩;Code.part22;dropfelt ⟨"%22"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%90"⟩;Code.part23;dropfelt ⟨"%25"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%94"⟩;Code.part24;dropfelt ⟨"%28"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%98"⟩;Code.part25;dropfelt ⟨"%31"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%102"⟩;Code.part26;dropfelt ⟨"%34"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%106"⟩;Code.part27;dropfelt ⟨"%37"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%110"⟩;Code.part28;dropfelt ⟨"%40"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%111"⟩;dropfelt ⟨"%114"⟩;Code.part29;dropfelt ⟨"%43"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%118"⟩;Code.part30;dropfelt ⟨"%46"⟩;dropfelt ⟨"%117"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%122"⟩;Code.part31;dropfelt ⟨"%49"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%123"⟩;dropfelt ⟨"%126"⟩;Code.part32;dropfelt ⟨"%52"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%130"⟩;Code.part33;dropfelt ⟨"%55"⟩;dropfelt ⟨"%129"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%134"⟩;Code.part34;dropfelt ⟨"%58"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%135"⟩;dropfelt ⟨"%138"⟩;Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%73"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩) = prog
  unfold Code.part7
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part7_state_update part7_drops part7_state
  rfl

lemma part7_updates_opaque {st : State} : 
  Code.getReturn (part6_state_update st) ↔
  Code.getReturn (part7_state_update (part6_drops (part6_state st))) := by
  simp [part6_state_update, part7_wp]

lemma part7_cumulative_wp {code0 data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 data18 data19: Felt} :
  Code.run (start_state ([code0]) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19])) ↔
  Code.getReturn
      (part7_state_update
        ((((((((((({
                                buffers :=
                                  ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                      [[some data0, some data1, some data2, some data3, some data4, some data5,
                                          some data6, some data7, some data8, some data9, some data10, some data11,
                                          some data12, some data13, some data14, some data15, some data16, some data17,
                                          some data18, some data19]])[{ name := "code" : BufferVar }] ←ₘ
                                    [[some code0]],
                                bufferWidths :=
                                  ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                      (20 : ℕ))[{ name := "code" : BufferVar }] ←ₘ
                                    (1 : ℕ),
                                cycle := (0 : ℕ), felts := Map.empty, isFailed := False, props := Map.empty,
                                vars :=
                                  [{ name := "code" : BufferVar },
                                    { name := "data" : BufferVar }] }[props][{ name := "%19" : PropVar }] ←
                              True)[felts][{ name := "%22" : FeltVar }] ←
                            data2)[felts][{ name := "%21" : FeltVar }] ←
                          data1)[felts][{ name := "%25" : FeltVar }] ←
                        data3)[felts][{ name := "%28" : FeltVar }] ←
                      data4)[felts][{ name := "%31" : FeltVar }] ←
                    data5)[felts][{ name := "%34" : FeltVar }] ←
                  data6)[felts][{ name := "%37" : FeltVar }] ←
                data7)[felts][{ name := "%39" : FeltVar }] ←
              data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) + data5 * (5 : Felt) +
                  data6 * (6 : Felt) +
                data7 * (7 : Felt))[felts][{ name := "%7" : FeltVar }] ←
            (8 : Felt))[felts][{ name := "%40" : FeltVar }] ←
          data8))  := by
    rewrite [part6_cumulative_wp]
    rewrite [part7_updates_opaque]
    unfold part6_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part6_drops
    -- 3 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths, State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.OneHot20.Constraints.WP