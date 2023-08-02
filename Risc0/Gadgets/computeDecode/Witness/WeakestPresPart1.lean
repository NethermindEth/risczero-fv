import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.computeDecode.Witness.Code
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart0

namespace Risc0.computeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part1 on st
def part1_state (st: State) : State :=
  
        (State.set!
          (State.set!
            ((State.set! st { name := "data" : BufferVar } (8 : ℕ)
                (Option.get! st.felts[{ name := "%3" : FeltVar }]!))[felts][{ name := "%7" : FeltVar }] ←
              (2 : Felt))
            { name := "data" : BufferVar } (0 : ℕ) (2 : Felt))
          { name := "data" : BufferVar } (13 : ℕ) (Option.get! st.felts[{ name := "%3" : FeltVar }]!)) 

def part1_drops (st: State) : State :=
  st

-- Run the program from part1 onwards by using part1_state rather than Code.part1
def part1_state_update (st: State): State :=
  Γ (part1_drops (part1_state st)) ⟦Code.part2;Code.part3;Code.part4;dropfelt ⟨"%3"⟩;Code.part5;Code.part6;dropfelt ⟨"%11"⟩;dropfelt ⟨"%13"⟩;Code.part7;dropfelt ⟨"%14"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%16"⟩;Code.part8;dropfelt ⟨"%12"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%10"⟩;Code.part9;dropfelt ⟨"%19"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%22"⟩;Code.part10;dropfelt ⟨"%23"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;Code.part11;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;Code.part12;dropfelt ⟨"%1"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;Code.part13;dropfelt ⟨"%28"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;Code.part14;dropfelt ⟨"%6"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;Code.part15;dropfelt ⟨"%5"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%44"⟩;Code.part16;dropfelt ⟨"%2"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%46"⟩;Code.part17;dropfelt ⟨"%42"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;Code.part18;dropfelt ⟨"%7"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part19;dropfelt ⟨"%8"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%57"⟩;Code.part20;dropfelt ⟨"%58"⟩⟧

-- Prove that substituting part1_state for Code.part1 produces the same result
lemma part1_wp {st : State} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part1;Code.part2;Code.part3;Code.part4;dropfelt ⟨"%3"⟩;Code.part5;Code.part6;dropfelt ⟨"%11"⟩;dropfelt ⟨"%13"⟩;Code.part7;dropfelt ⟨"%14"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%16"⟩;Code.part8;dropfelt ⟨"%12"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%10"⟩;Code.part9;dropfelt ⟨"%19"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%22"⟩;Code.part10;dropfelt ⟨"%23"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;Code.part11;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;Code.part12;dropfelt ⟨"%1"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;Code.part13;dropfelt ⟨"%28"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;Code.part14;dropfelt ⟨"%6"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;Code.part15;dropfelt ⟨"%5"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%44"⟩;Code.part16;dropfelt ⟨"%2"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%46"⟩;Code.part17;dropfelt ⟨"%42"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;Code.part18;dropfelt ⟨"%7"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part19;dropfelt ⟨"%8"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%57"⟩;Code.part20;dropfelt ⟨"%58"⟩) st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn (part1_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part2;Code.part3;Code.part4;dropfelt ⟨"%3"⟩;Code.part5;Code.part6;dropfelt ⟨"%11"⟩;dropfelt ⟨"%13"⟩;Code.part7;dropfelt ⟨"%14"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%16"⟩;Code.part8;dropfelt ⟨"%12"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%10"⟩;Code.part9;dropfelt ⟨"%19"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%22"⟩;Code.part10;dropfelt ⟨"%23"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;Code.part11;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;Code.part12;dropfelt ⟨"%1"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;Code.part13;dropfelt ⟨"%28"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;Code.part14;dropfelt ⟨"%6"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;Code.part15;dropfelt ⟨"%5"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%44"⟩;Code.part16;dropfelt ⟨"%2"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%46"⟩;Code.part17;dropfelt ⟨"%42"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;Code.part18;dropfelt ⟨"%7"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part19;dropfelt ⟨"%8"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%57"⟩;Code.part20;dropfelt ⟨"%58"⟩) = prog
  unfold Code.part1
  MLIR
  rewrite [←eq]
  
  unfold part1_state_update part1_drops part1_state
  rfl

lemma part1_updates_opaque {st : State} : 
  Code.getReturn (part0_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn (part1_state_update (part0_drops (part0_state st))) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) := by
  simp [part0_state_update, part1_wp]

lemma part1_cumulative_wp {in0: Felt} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17: Option Felt} :
  Code.run (start_state ([in0])) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn
      (part1_state_update
        {
          buffers :=
            (Map.empty[{ name := "in" : BufferVar }] ←ₘ [[some in0]])[{ name := "data" : BufferVar }] ←ₘ
              [[none, some (0 : Felt), none, none, none, none, none, none, none, some (0 : Felt), some (0 : Felt), none,
                  none, none, none, none, none, none]],
          bufferWidths :=
            ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ (18 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
              (1 : ℕ),
          cycle := (0 : ℕ), felts := (fun x => Map.empty x)[{ name := "%3" : FeltVar }] ←ₘ (0 : Felt),
          isFailed := False, props := Map.empty,
          vars := [{ name := "in" : BufferVar }, { name := "data" : BufferVar }] })
      ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14,
        data15, data16, data17])  := by
    rewrite [part0_cumulative_wp]
    rewrite [part1_updates_opaque]
    unfold part0_state
    try simplify_get_hack
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part0_drops
    -- 0 drops
    -- simp only [State.drop_update_swap, State.drop_update_same]
    -- rewrite [State.dropFelts]
    -- simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 3 sets
    rewrite [Map.drop_of_updates]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.computeDecode.Witness.WP