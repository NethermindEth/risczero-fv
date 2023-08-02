import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.computeDecode.Constraints.Code
import Risc0.Gadgets.computeDecode.Constraints.WeakestPresPart3

namespace Risc0.computeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part4 on st
def part4_state (st: State) : State :=
  
        ((((st[felts][{ name := "%21" : FeltVar }] ←
                Option.get! (State.felts st { name := "%20" : FeltVar }) *
                  Option.get! (State.felts st { name := "%7" : FeltVar }))[felts][{ name := "%22" : FeltVar }] ←
              Option.get! (State.felts st { name := "%20" : FeltVar }) *
                  Option.get! (State.felts st { name := "%7" : FeltVar }) +
                Option.get! (State.felts st { name := "%19" : FeltVar }))[felts][{ name := "%1" : FeltVar }] ←
            (2 : Felt))[felts][{ name := "%23" : FeltVar }] ←
          (Option.get! (State.felts st { name := "%20" : FeltVar }) *
                Option.get! (State.felts st { name := "%7" : FeltVar }) +
              Option.get! (State.felts st { name := "%19" : FeltVar })) *
            (2 : Felt)) 

def part4_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%19"⟩) ⟨"%7"⟩) ⟨"%20"⟩) ⟨"%21"⟩) ⟨"%22"⟩

-- Run the program from part4 onwards by using part4_state rather than Code.part4
def part4_state_update (st: State): State :=
  Γ (part4_drops (part4_state st)) ⟦Code.part5;dropfelt ⟨"%23"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;Code.part6;dropfelt ⟨"%28"⟩;dropfelt ⟨"%31"⟩;Code.part7;dropfelt ⟨"%6"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;Code.part8;dropfelt ⟨"%29"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;Code.part9;dropfelt ⟨"%38"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%40"⟩;Code.part10;dropfelt ⟨"%3"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%46"⟩;Code.part11;dropfelt ⟨"%5"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%48"⟩;Code.part12;dropfelt ⟨"%44"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;Code.part13;dropfelt ⟨"%1"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;Code.part14;dropfelt ⟨"%4"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%57"⟩;Code.part15;dropfelt ⟨"%60"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%61"⟩⟧

-- Prove that substituting part4_state for Code.part4 produces the same result
lemma part4_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part4;dropfelt ⟨"%19"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%22"⟩;Code.part5;dropfelt ⟨"%23"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;Code.part6;dropfelt ⟨"%28"⟩;dropfelt ⟨"%31"⟩;Code.part7;dropfelt ⟨"%6"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;Code.part8;dropfelt ⟨"%29"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;Code.part9;dropfelt ⟨"%38"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%40"⟩;Code.part10;dropfelt ⟨"%3"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%46"⟩;Code.part11;dropfelt ⟨"%5"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%48"⟩;Code.part12;dropfelt ⟨"%44"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;Code.part13;dropfelt ⟨"%1"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;Code.part14;dropfelt ⟨"%4"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%57"⟩;Code.part15;dropfelt ⟨"%60"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%61"⟩) st) ↔
  Code.getReturn (part4_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%19"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%22"⟩;Code.part5;dropfelt ⟨"%23"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;Code.part6;dropfelt ⟨"%28"⟩;dropfelt ⟨"%31"⟩;Code.part7;dropfelt ⟨"%6"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;Code.part8;dropfelt ⟨"%29"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;Code.part9;dropfelt ⟨"%38"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%40"⟩;Code.part10;dropfelt ⟨"%3"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%46"⟩;Code.part11;dropfelt ⟨"%5"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%48"⟩;Code.part12;dropfelt ⟨"%44"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;Code.part13;dropfelt ⟨"%1"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;Code.part14;dropfelt ⟨"%4"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%57"⟩;Code.part15;dropfelt ⟨"%60"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%61"⟩) = prog
  unfold Code.part4
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part4_state_update part4_drops part4_state
  rfl

lemma part4_updates_opaque {st : State} : 
  Code.getReturn (part3_state_update st) ↔
  Code.getReturn (part4_state_update (part3_drops (part3_state st))) := by
  simp [part3_state_update, part4_wp]

lemma part4_cumulative_wp {in0 data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17: Felt} :
  Code.run (start_state ([in0]) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17])) ↔
  Code.getReturn
      (part4_state_update
        ((((((({
                        buffers :=
                          ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                              [[some data0, some data1, some data2, some data3, some data4, some data5, some data6,
                                  some data7, some data8, some data9, some data10, some data11, some data12,
                                  some data13, some data14, some data15, some data16,
                                  some data17]])[{ name := "in" : BufferVar }] ←ₘ
                            [[some in0]],
                        bufferWidths :=
                          ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                              (18 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                            (1 : ℕ),
                        cycle := (0 : ℕ), felts := Map.empty, isFailed := False, props := Map.empty,
                        vars :=
                          [{ name := "in" : BufferVar },
                            { name := "data" : BufferVar }] }[props][{ name := "%8" : PropVar }] ←
                      True)[felts][{ name := "%3" : FeltVar }] ←
                    (4 : Felt))[felts][{ name := "%6" : FeltVar }] ←
                  (8 : Felt))[felts][{ name := "%5" : FeltVar }] ←
                (16 : Felt))[felts][{ name := "%19" : FeltVar }] ←
              data1 * (16 : Felt) + data9 * (8 : Felt) + data8 * (4 : Felt) +
                data0)[felts][{ name := "%7" : FeltVar }] ←
            (64 : Felt))[felts][{ name := "%20" : FeltVar }] ←
          data10))  := by
    rewrite [part3_cumulative_wp]
    rewrite [part4_updates_opaque]
    unfold part3_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part3_drops
    -- 2 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.computeDecode.Constraints.WP