import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.computeDecode.Witness.Code
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart19

namespace Risc0.computeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part20 on st
def part20_state (st: State) : State :=
   (withEqZero (Option.get! st.felts[{ name := "%58" : FeltVar }]!) st) 

def part20_drops (st: State) : State :=
  State.dropFelts (st) ⟨"%58"⟩

-- Run the program from part20 onwards by using part20_state rather than Code.part20
def part20_state_update (st: State): State :=
  part20_drops (part20_state st)

-- Prove that substituting part20_state for Code.part20 produces the same result
lemma part20_wp {st : State} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part20;dropfelt ⟨"%58"⟩) st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn (part20_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%58"⟩) = prog
  unfold Code.part20
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_dropfelt]
  unfold part20_state_update part20_drops part20_state
  rfl

lemma part20_updates_opaque {st : State} : 
  Code.getReturn (part19_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn (part20_state_update (part19_drops (part19_state st))) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) := by
  simp [part19_state_update, part20_wp]

lemma part20_cumulative_wp {in0: Felt} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17: Option Felt} :
  Code.run (start_state ([in0])) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn
      (part20_state_update
        ({
            buffers :=
              ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ [[some in0]])[{ name := "data" : BufferVar }] ←ₘ
                [[some (2 : Felt), some (0 : Felt), some (0 : Felt), some (3 : Felt), some (0 : Felt), some (0 : Felt),
                    some (2 : Felt), some (0 : Felt), some (0 : Felt), some (0 : Felt), some (0 : Felt),
                    some (0 : Felt), some (0 : Felt), some (0 : Felt), some (0 : Felt), some (0 : Felt),
                    some (0 : Felt), some (1 : Felt)]],
            bufferWidths :=
              ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ (18 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                (1 : ℕ),
            cycle := (0 : ℕ), felts := Map.empty, isFailed := False, props := Map.empty,
            vars :=
              [{ name := "in" : BufferVar }, { name := "data" : BufferVar }] }[felts][{ name := "%58" : FeltVar }] ←
          (0 : Felt)))
      ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14,
        data15, data16, data17])  := by
    rewrite [part19_cumulative_wp]
    rewrite [part20_updates_opaque]
    unfold part19_state
    try simplify_get_hack
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part19_drops
    -- 6 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are statements after an if
    try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

lemma closed_form {in0: Felt} :
  Code.run (start_state [in0]) ([data0,data1,data2,data3,data4,data5,data6,data7,data8,data9,data10,data11,data12,data13,data14,data15,data16,data17]) ↔
   some (2 : Felt) = data0 ∧
      some (0 : Felt) = data1 ∧
        some (0 : Felt) = data2 ∧
          some (3 : Felt) = data3 ∧
            some (0 : Felt) = data4 ∧
              some (0 : Felt) = data5 ∧
                some (2 : Felt) = data6 ∧
                  some (0 : Felt) = data7 ∧
                    some (0 : Felt) = data8 ∧
                      some (0 : Felt) = data9 ∧
                        some (0 : Felt) = data10 ∧
                          some (0 : Felt) = data11 ∧
                            some (0 : Felt) = data12 ∧
                              some (0 : Felt) = data13 ∧
                                some (0 : Felt) = data14 ∧
                                  some (0 : Felt) = data15 ∧ some (0 : Felt) = data16 ∧ some (1 : Felt) = data17  := by
    rewrite [part20_cumulative_wp]
    unfold part20_state_update
    unfold part20_state
    try simplify_get_hack
    MLIR_states_updates
    -- 1 withEqZero
    rewrite [withEqZero_def]
    MLIR_states_updates
    unfold part20_drops
    -- 1 drop
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are statements after an if
    try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]
    unfold Code.getReturn
    simp only
    simp [Map.update_get_wobbly, List.getLast!]
end Risc0.computeDecode.Witness.WP