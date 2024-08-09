import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.computeDecode.Constraints.Code
import Risc0.Gadgets.computeDecode.Constraints.WeakestPresPart13

namespace Risc0.computeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part14 on st
def part14_state (st: State) : State :=
  
        ((((st["%58"] ←ₛ
                getImpl st { name := "data" : BufferVar } (0 : Back) (16 : ℕ))[felts][{ name := "%59" : FeltVar }] ←
              ((st["%58"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (16 : ℕ)).felts
                    { name := "%58" : FeltVar }).get! *
                (st.felts { name := "%4" : FeltVar }).get!)["%57"] ←ₛ
            getImpl st { name := "data" : BufferVar } (0 : Back) (17 : ℕ))[felts][{ name := "%60" : FeltVar }] ←
          ((st["%58"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (16 : ℕ)).felts
                  { name := "%58" : FeltVar }).get! *
              (st.felts { name := "%4" : FeltVar }).get! +
            ((((st["%58"] ←ₛ
                        getImpl st { name := "data" : BufferVar } (0 : Back)
                          (16 : ℕ))[felts][{ name := "%59" : FeltVar }] ←
                      ((st["%58"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (16 : ℕ)).felts
                            { name := "%58" : FeltVar }).get! *
                        (st.felts { name := "%4" : FeltVar }).get!)["%57"] ←ₛ
                    getImpl st { name := "data" : BufferVar } (0 : Back) (17 : ℕ)).felts
                { name := "%57" : FeltVar }).get!) 

def part14_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%4"⟩) ⟨"%58"⟩) ⟨"%59"⟩) ⟨"%57"⟩

-- Run the program from part14 onwards by using part14_state rather than Code.part14
def part14_state_update (st: State): State :=
  Γ (part14_drops (part14_state st)) ⟦Code.part15;dropfelt ⟨"%60"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%61"⟩⟧

-- Prove that substituting part14_state for Code.part14 produces the same result
lemma part14_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part14;dropfelt ⟨"%4"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%57"⟩;Code.part15;dropfelt ⟨"%60"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%61"⟩) st) ↔
  Code.getReturn (part14_state_update st) := by
  unfold MLIR.runProgram; try simp only
  generalize eq : (dropfelt ⟨"%4"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%57"⟩;Code.part15;dropfelt ⟨"%60"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%61"⟩) = prog
  unfold Code.part14
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part14_state_update part14_drops part14_state
  rfl

lemma part14_updates_opaque {st : State} : 
  Code.getReturn (part13_state_update st) ↔
  Code.getReturn (part14_state_update (part13_drops (part13_state st))) := by
  try simp [part13_state_update, part14_wp]

lemma part14_cumulative_wp {in0 data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17: Felt} :
  Code.run (start_state ([in0]) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17])) ↔
  Code.getReturn
      (part14_state_update
        ((((({
                    buffers :=
                      (Map.empty[{ name := "data" : BufferVar }] ←ₘ
                          [[some data0, some data1, some data2, some data3, some data4, some data5, some data6,
                              some data7, some data8, some data9, some data10, some data11, some data12, some data13,
                              some data14, some data15, some data16, some data17]])[{ name := "in" : BufferVar }] ←ₘ
                        [[some in0]],
                    bufferWidths :=
                      (Map.empty[{ name := "data" : BufferVar }] ←ₘ (18 : ℕ))[{ name := "in" : BufferVar }] ←ₘ (1 : ℕ),
                    cycle := (0 : ℕ), felts := Map.empty, isFailed := False, props := Map.empty,
                    vars :=
                      [{ name := "in" : BufferVar },
                        { name := "data" : BufferVar }] }[props][{ name := "%8" : PropVar }] ←
                  True)[props][{ name := "%26" : PropVar }] ←
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
                  (0 : Felt)))[felts][{ name := "%4" : FeltVar }] ←
            (128 : Felt))[props][{ name := "%56" : PropVar }] ←
          (((4 : Felt) -
                  ((data10 * (64 : Felt) + (data1 * (16 : Felt) + data9 * (8 : Felt) + data8 * (4 : Felt) + data0)) *
                      (2 : Felt) +
                    data13) =
                (0 : Felt) ∧
              (3 : Felt) -
                  ((data12 * (8 : Felt) + data2 * (2 : Felt) + data11) * (16 : Felt) + data4 * (4 : Felt) + data3) =
                (0 : Felt)) ∧
            (2 : Felt) -
                (data14 * (128 : Felt) + (data15 * (4 : Felt) + data5) * (16 : Felt) + data7 * (4 : Felt) + data6) =
              (0 : Felt))))  := by
    rewrite [part13_cumulative_wp]
    rewrite [part14_updates_opaque]
    unfold part13_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part13_drops
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