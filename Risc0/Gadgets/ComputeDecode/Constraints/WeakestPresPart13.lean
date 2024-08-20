import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart12

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part13 on st
def part13_state (st: State) : State :=
  
        ((((st[felts][{ name := "%55" : FeltVar }] ←
                (st.felts { name := "%54" : FeltVar }).get! + (st.felts { name := "%46" : FeltVar }).get!)["%44"] ←ₛ
              getImpl st { name := "data" : BufferVar } (0 : Back) (6 : ℕ))[felts][{ name := "%56" : FeltVar }] ←
            (st.felts { name := "%54" : FeltVar }).get! + (st.felts { name := "%46" : FeltVar }).get! +
              (((st[felts][{ name := "%55" : FeltVar }] ←
                        (st.felts { name := "%54" : FeltVar }).get! +
                          (st.felts { name := "%46" : FeltVar }).get!)["%44"] ←ₛ
                      getImpl st { name := "data" : BufferVar } (0 : Back) (6 : ℕ)).felts
                  { name := "%44" : FeltVar }).get!)["%8"] ←ₛ
          getImpl st { name := "in" : BufferVar } (0 : Back) (1 : ℕ)) 

def part13_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%46"⟩) ⟨"%54"⟩) ⟨"%55"⟩) ⟨"%44"⟩

-- Run the program from part13 onwards by using part13_state rather than Code.part13
def part13_state_update (st: State): State :=
  Γ (part13_drops (part13_state st)) ⟦Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%63"⟩⟧

-- Prove that substituting part13_state for Code.part13 produces the same result
lemma part13_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part13;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%63"⟩) st) ↔
  Code.getReturn (part13_state_update st) := by
  unfold MLIR.runProgram; try simp only
  generalize eq : (dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%63"⟩) = prog
  unfold Code.part13
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part13_state_update part13_drops part13_state
  rfl

lemma part13_updates_opaque {st : State} : 
  Code.getReturn (part12_state_update st) ↔
  Code.getReturn (part13_state_update (part12_drops (part12_state st))) := by
  try simp [part12_state_update, part13_wp]

lemma part13_cumulative_wp {in0 in1 in2 in3 data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17: Felt} :
  Code.run (start_state ([in0, in1, in2, in3]) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17])) ↔
  Code.getReturn
      (part13_state_update
        (((((({
                      buffers :=
                        (Map.empty[{ name := "data" : BufferVar }] ←ₘ
                            [[some data0, some data1, some data2, some data3, some data4, some data5, some data6,
                                some data7, some data8, some data9, some data10, some data11, some data12, some data13,
                                some data14, some data15, some data16, some data17]])[{ name := "in" : BufferVar }] ←ₘ
                          [[some in0, some in1, some in2, some in3]],
                      bufferWidths :=
                        (Map.empty[{ name := "data" : BufferVar }] ←ₘ (18 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                          (4 : ℕ),
                      cycle := (0 : ℕ), felts := Map.empty, isFailed := False, props := Map.empty,
                      vars :=
                        [{ name := "in" : BufferVar },
                          { name := "data" : BufferVar }] }[props][{ name := "%6" : PropVar }] ←
                    True)[props][{ name := "%28" : PropVar }] ←
                  in3 -
                      ((data10 * (64 : Felt) +
                            (data1 * (16 : Felt) + data9 * (8 : Felt) + data8 * (4 : Felt) + data0)) *
                          (2 : Felt) +
                        data13) =
                    (0 : Felt))[props][{ name := "%43" : PropVar }] ←
                (in3 -
                      ((data10 * (64 : Felt) +
                            (data1 * (16 : Felt) + data9 * (8 : Felt) + data8 * (4 : Felt) + data0)) *
                          (2 : Felt) +
                        data13) =
                    (0 : Felt) ∧
                  in2 -
                      ((data12 * (8 : Felt) + data2 * (2 : Felt) + data11) * (16 : Felt) + data4 * (4 : Felt) + data3) =
                    (0 : Felt)))[felts][{ name := "%46" : FeltVar }] ←
              data7 * (4 : Felt))[felts][{ name := "%0" : FeltVar }] ←
            (128 : Felt))[felts][{ name := "%54" : FeltVar }] ←
          data14 * (128 : Felt) + (data15 * (4 : Felt) + data5) * (16 : Felt)))  := by
    rewrite [part12_cumulative_wp]
    rewrite [part13_updates_opaque]
    unfold part12_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part12_drops
    -- 3 drops
    try simp [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    try simp [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    try simp [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- try simp [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.ComputeDecode.Constraints.WP