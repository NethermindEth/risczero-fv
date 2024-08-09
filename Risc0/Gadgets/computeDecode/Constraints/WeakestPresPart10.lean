import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.computeDecode.Constraints.Code
import Risc0.Gadgets.computeDecode.Constraints.WeakestPresPart9

namespace Risc0.computeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part10 on st
def part10_state (st: State) : State :=
  
        ((((st["%43"] ←ₛ
                getImpl st { name := "data" : BufferVar } (0 : Back) (7 : ℕ))[felts][{ name := "%44" : FeltVar }] ←
              ((st["%43"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (7 : ℕ)).felts
                    { name := "%43" : FeltVar }).get! *
                (st.felts { name := "%3" : FeltVar }).get!)["%46"] ←ₛ
            getImpl st { name := "data" : BufferVar } (0 : Back) (15 : ℕ))[felts][{ name := "%47" : FeltVar }] ←
          ((((st["%43"] ←ₛ
                        getImpl st { name := "data" : BufferVar } (0 : Back)
                          (7 : ℕ))[felts][{ name := "%44" : FeltVar }] ←
                      ((st["%43"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (7 : ℕ)).felts
                            { name := "%43" : FeltVar }).get! *
                        (st.felts { name := "%3" : FeltVar }).get!)["%46"] ←ₛ
                    getImpl st { name := "data" : BufferVar } (0 : Back) (15 : ℕ)).felts
                { name := "%46" : FeltVar }).get! *
            (st.felts { name := "%3" : FeltVar }).get!) 

def part10_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%3"⟩) ⟨"%43"⟩) ⟨"%46"⟩

-- Run the program from part10 onwards by using part10_state rather than Code.part10
def part10_state_update (st: State): State :=
  Γ (part10_drops (part10_state st)) ⟦Code.part11;dropfelt ⟨"%5"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%48"⟩;Code.part12;dropfelt ⟨"%44"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;Code.part13;dropfelt ⟨"%1"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;Code.part14;dropfelt ⟨"%4"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%57"⟩;Code.part15;dropfelt ⟨"%60"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%61"⟩⟧

-- Prove that substituting part10_state for Code.part10 produces the same result
lemma part10_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part10;dropfelt ⟨"%3"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%46"⟩;Code.part11;dropfelt ⟨"%5"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%48"⟩;Code.part12;dropfelt ⟨"%44"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;Code.part13;dropfelt ⟨"%1"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;Code.part14;dropfelt ⟨"%4"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%57"⟩;Code.part15;dropfelt ⟨"%60"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%61"⟩) st) ↔
  Code.getReturn (part10_state_update st) := by
  unfold MLIR.runProgram; try simp only
  generalize eq : (dropfelt ⟨"%3"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%46"⟩;Code.part11;dropfelt ⟨"%5"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%48"⟩;Code.part12;dropfelt ⟨"%44"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;Code.part13;dropfelt ⟨"%1"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;Code.part14;dropfelt ⟨"%4"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%57"⟩;Code.part15;dropfelt ⟨"%60"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%61"⟩) = prog
  unfold Code.part10
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part10_state_update part10_drops part10_state
  rfl

lemma part10_updates_opaque {st : State} : 
  Code.getReturn (part9_state_update st) ↔
  Code.getReturn (part10_state_update (part9_drops (part9_state st))) := by
  try simp [part9_state_update, part10_wp]

lemma part10_cumulative_wp {in0 data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17: Felt} :
  Code.run (start_state ([in0]) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17])) ↔
  Code.getReturn
      (part10_state_update
        (((((({
                      buffers :=
                        (Map.empty[{ name := "data" : BufferVar }] ←ₘ
                            [[some data0, some data1, some data2, some data3, some data4, some data5, some data6,
                                some data7, some data8, some data9, some data10, some data11, some data12, some data13,
                                some data14, some data15, some data16, some data17]])[{ name := "in" : BufferVar }] ←ₘ
                          [[some in0]],
                      bufferWidths :=
                        (Map.empty[{ name := "data" : BufferVar }] ←ₘ (18 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                          (1 : ℕ),
                      cycle := (0 : ℕ), felts := Map.empty, isFailed := False, props := Map.empty,
                      vars :=
                        [{ name := "in" : BufferVar },
                          { name := "data" : BufferVar }] }[props][{ name := "%8" : PropVar }] ←
                    True)[felts][{ name := "%3" : FeltVar }] ←
                  (4 : Felt))[felts][{ name := "%5" : FeltVar }] ←
                (16 : Felt))[felts][{ name := "%1" : FeltVar }] ←
              (2 : Felt))[props][{ name := "%26" : PropVar }] ←
            (4 : Felt) -
                ((data10 * (64 : Felt) + (data1 * (16 : Felt) + data9 * (8 : Felt) + data8 * (4 : Felt) + data0)) *
                    (2 : Felt) +
                  data13) =
              (0 : Felt))[props][{ name := "%41" : PropVar }] ←
          ((4 : Felt) -
                ((data10 * (64 : Felt) + (data1 * (16 : Felt) + data9 * (8 : Felt) + data8 * (4 : Felt) + data0)) *
                    (2 : Felt) +
                  data13) =
              (0 : Felt) ∧
            (3 : Felt) -
                ((data12 * (8 : Felt) + data2 * (2 : Felt) + data11) * (16 : Felt) + data4 * (4 : Felt) + data3) =
              (0 : Felt))))  := by
    rewrite [part9_cumulative_wp]
    rewrite [part10_updates_opaque]
    unfold part9_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part9_drops
    -- 5 drops
    try simp [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    try simp [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    try simp [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- try simp [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.computeDecode.Constraints.WP