import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.computeDecode.Witness.Code
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart18

namespace Risc0.computeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part19 on st
def part19_state (st: State) : State :=
  
        ((((st[felts][{ name := "%56" : FeltVar }] ←
                (st.felts { name := "%55" : FeltVar }).get! * (st.felts { name := "%4" : FeltVar }).get!)["%54"] ←ₛ
              getImpl st { name := "data" : BufferVar } (0 : Back) (17 : ℕ))[felts][{ name := "%57" : FeltVar }] ←
            (st.felts { name := "%55" : FeltVar }).get! * (st.felts { name := "%4" : FeltVar }).get! +
              (((st[felts][{ name := "%56" : FeltVar }] ←
                        (st.felts { name := "%55" : FeltVar }).get! *
                          (st.felts { name := "%4" : FeltVar }).get!)["%54"] ←ₛ
                      getImpl st { name := "data" : BufferVar } (0 : Back) (17 : ℕ)).felts
                  { name := "%54" : FeltVar }).get!)[felts][{ name := "%58" : FeltVar }] ←
          (st.felts { name := "%8" : FeltVar }).get! -
            ((st.felts { name := "%55" : FeltVar }).get! * (st.felts { name := "%4" : FeltVar }).get! +
              (((st[felts][{ name := "%56" : FeltVar }] ←
                        (st.felts { name := "%55" : FeltVar }).get! *
                          (st.felts { name := "%4" : FeltVar }).get!)["%54"] ←ₛ
                      getImpl st { name := "data" : BufferVar } (0 : Back) (17 : ℕ)).felts
                  { name := "%54" : FeltVar }).get!)) 

def part19_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%8"⟩) ⟨"%4"⟩) ⟨"%55"⟩) ⟨"%56"⟩) ⟨"%54"⟩) ⟨"%57"⟩

-- Run the program from part19 onwards by using part19_state rather than Code.part19
def part19_state_update (st: State): State :=
  Γ (part19_drops (part19_state st)) ⟦Code.part20;dropfelt ⟨"%58"⟩⟧

-- Prove that substituting part19_state for Code.part19 produces the same result
lemma part19_wp {st : State} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part19;dropfelt ⟨"%8"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%57"⟩;Code.part20;dropfelt ⟨"%58"⟩) st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn (part19_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) := by
  unfold MLIR.runProgram; try simp only
  generalize eq : (dropfelt ⟨"%8"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%57"⟩;Code.part20;dropfelt ⟨"%58"⟩) = prog
  unfold Code.part19
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part19_state_update part19_drops part19_state
  rfl

lemma part19_updates_opaque {st : State} : 
  Code.getReturn (part18_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn (part19_state_update (part18_drops (part18_state st))) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) := by
  try simp [part18_state_update, part19_wp]

lemma part19_cumulative_wp {in0: Felt} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17: Option Felt} :
  Code.run (start_state ([in0])) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn
      (part19_state_update
        ({
            buffers :=
              (Map.empty[{ name := "in" : BufferVar }] ←ₘ [[some in0]])[{ name := "data" : BufferVar }] ←ₘ
                [[some (2 : Felt), some (0 : Felt), some (0 : Felt), some (3 : Felt), some (0 : Felt), some (0 : Felt),
                    some (2 : Felt), some (0 : Felt), some (0 : Felt), some (0 : Felt), some (0 : Felt),
                    some (0 : Felt), some (0 : Felt), some (0 : Felt), some (0 : Felt), some (0 : Felt),
                    some (0 : Felt), some (1 : Felt)]],
            bufferWidths :=
              (Map.empty[{ name := "data" : BufferVar }] ←ₘ (18 : ℕ))[{ name := "in" : BufferVar }] ←ₘ (1 : ℕ),
            cycle := (0 : ℕ),
            felts := (Map.empty[{ name := "%8" : FeltVar }] ←ₘ (1 : Felt))[{ name := "%4" : FeltVar }] ←ₘ (128 : Felt),
            isFailed := ¬(4 : Felt) - (2 : Felt) * (2 : Felt) = (0 : Felt), props := Map.empty,
            vars :=
              [{ name := "in" : BufferVar }, { name := "data" : BufferVar }] }[felts][{ name := "%55" : FeltVar }] ←
          (0 : Felt)))
      ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14,
        data15, data16, data17])  := by
    rewrite [part18_cumulative_wp]
    rewrite [part19_updates_opaque]
    unfold part18_state
    try simplify_get_hack
    MLIR_states_updates
    -- 1 withEqZero
    rewrite [withEqZero_def]
    MLIR_states_updates
    unfold part18_drops
    -- 5 drops
    try simp [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    try simp [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    try simp [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- try simp [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.computeDecode.Witness.WP