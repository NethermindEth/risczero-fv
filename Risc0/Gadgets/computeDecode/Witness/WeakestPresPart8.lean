import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.computeDecode.Witness.Code
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart7

namespace Risc0.computeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part8 on st
def part8_state (st: State) : State :=
  
        ((((st[felts][{ name := "%18" : FeltVar }] ←
                Option.get! (State.felts st { name := "%17" : FeltVar }) +
                  Option.get! (State.felts st { name := "%12" : FeltVar }))["%10"] ←ₛ
              getImpl st { name := "data" : BufferVar } (0 : Back) (0 : ℕ))[felts][{ name := "%19" : FeltVar }] ←
            Option.get! (State.felts st { name := "%17" : FeltVar }) +
                Option.get! (State.felts st { name := "%12" : FeltVar }) +
              Option.get!
                (State.felts
                  ((st[felts][{ name := "%18" : FeltVar }] ←
                      Option.get! (State.felts st { name := "%17" : FeltVar }) +
                        Option.get! (State.felts st { name := "%12" : FeltVar }))["%10"] ←ₛ
                    getImpl st { name := "data" : BufferVar } (0 : Back) (0 : ℕ))
                  { name := "%10" : FeltVar }))[felts][{ name := "%0" : FeltVar }] ←
          (64 : Felt)) 

def part8_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%12"⟩) ⟨"%17"⟩) ⟨"%18"⟩) ⟨"%10"⟩

-- Run the program from part8 onwards by using part8_state rather than Code.part8
def part8_state_update (st: State): State :=
  Γ (part8_drops (part8_state st)) ⟦Code.part9;dropfelt ⟨"%19"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%22"⟩;Code.part10;dropfelt ⟨"%23"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;Code.part11;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;Code.part12;dropfelt ⟨"%1"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;Code.part13;dropfelt ⟨"%28"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;Code.part14;dropfelt ⟨"%6"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;Code.part15;dropfelt ⟨"%5"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%44"⟩;Code.part16;dropfelt ⟨"%2"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%46"⟩;Code.part17;dropfelt ⟨"%42"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;Code.part18;dropfelt ⟨"%7"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part19;dropfelt ⟨"%8"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%57"⟩;Code.part20;dropfelt ⟨"%58"⟩⟧

-- Prove that substituting part8_state for Code.part8 produces the same result
lemma part8_wp {st : State} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part8;dropfelt ⟨"%12"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%10"⟩;Code.part9;dropfelt ⟨"%19"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%22"⟩;Code.part10;dropfelt ⟨"%23"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;Code.part11;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;Code.part12;dropfelt ⟨"%1"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;Code.part13;dropfelt ⟨"%28"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;Code.part14;dropfelt ⟨"%6"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;Code.part15;dropfelt ⟨"%5"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%44"⟩;Code.part16;dropfelt ⟨"%2"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%46"⟩;Code.part17;dropfelt ⟨"%42"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;Code.part18;dropfelt ⟨"%7"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part19;dropfelt ⟨"%8"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%57"⟩;Code.part20;dropfelt ⟨"%58"⟩) st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn (part8_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%12"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%10"⟩;Code.part9;dropfelt ⟨"%19"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%22"⟩;Code.part10;dropfelt ⟨"%23"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;Code.part11;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;Code.part12;dropfelt ⟨"%1"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;Code.part13;dropfelt ⟨"%28"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;Code.part14;dropfelt ⟨"%6"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;Code.part15;dropfelt ⟨"%5"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%44"⟩;Code.part16;dropfelt ⟨"%2"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%46"⟩;Code.part17;dropfelt ⟨"%42"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;Code.part18;dropfelt ⟨"%7"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part19;dropfelt ⟨"%8"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%57"⟩;Code.part20;dropfelt ⟨"%58"⟩) = prog
  unfold Code.part8
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part8_state_update part8_drops part8_state
  rfl

lemma part8_updates_opaque {st : State} : 
  Code.getReturn (part7_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn (part8_state_update (part7_drops (part7_state st))) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) := by
  simp [part7_state_update, part8_wp]

lemma part8_cumulative_wp {in0: Felt} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17: Option Felt} :
  Code.run (start_state ([in0])) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn
      (part8_state_update
        ((((({
                    buffers :=
                      ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                          [[some in0]])[{ name := "data" : BufferVar }] ←ₘ
                        [[some (2 : Felt), some (0 : Felt), some (0 : Felt), some (3 : Felt), some (0 : Felt),
                            some (0 : Felt), some (2 : Felt), some (0 : Felt), some (0 : Felt), some (0 : Felt),
                            some (0 : Felt), some (0 : Felt), some (0 : Felt), some (0 : Felt), some (0 : Felt),
                            some (0 : Felt), some (0 : Felt), some (1 : Felt)]],
                    bufferWidths :=
                      ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                          (18 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                        (1 : ℕ),
                    cycle := (0 : ℕ),
                    felts :=
                      ((Map.empty[{ name := "%7" : FeltVar }] ←ₘ (2 : Felt))[{ name := "%6" : FeltVar }] ←ₘ
                          (3 : Felt))[{ name := "%8" : FeltVar }] ←ₘ
                        (1 : Felt),
                    isFailed := False, props := Map.empty,
                    vars :=
                      [{ name := "in" : BufferVar },
                        { name := "data" : BufferVar }] }[felts][{ name := "%5" : FeltVar }] ←
                  (4 : Felt))[felts][{ name := "%12" : FeltVar }] ←
                (0 : Felt) * (4 : Felt))[felts][{ name := "%1" : FeltVar }] ←
              (8 : Felt))[felts][{ name := "%2" : FeltVar }] ←
            (16 : Felt))[felts][{ name := "%17" : FeltVar }] ←
          (0 : Felt) * (16 : Felt) + (0 : Felt) * (8 : Felt)))
      ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14,
        data15, data16, data17])  := by
    rewrite [part7_cumulative_wp]
    rewrite [part8_updates_opaque]
    unfold part7_state
    try simplify_get_hack
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part7_drops
    -- 3 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.computeDecode.Witness.WP