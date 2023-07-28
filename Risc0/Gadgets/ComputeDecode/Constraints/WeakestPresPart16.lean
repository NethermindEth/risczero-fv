import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart15

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part16 on st
def part16_state (st: State) : State :=
  
        (st[props][{ name := "%64" : PropVar }] ←
          (Option.get! (State.props st { name := "%58" : PropVar }) ∧
            Option.get! (State.felts st { name := "%63" : FeltVar }) = (0 : Felt))) 

def part16_drops (st: State) : State :=
  State.dropFelts (st) ⟨"%63"⟩

-- Run the program from part16 onwards by using part16_state rather than Code.part16
def part16_state_update (st: State): State :=
  part16_drops (part16_state st)

-- Prove that substituting part16_state for Code.part16 produces the same result
lemma part16_wp {st : State}:
  Code.getReturn (MLIR.runProgram (Code.part16;dropfelt ⟨"%63"⟩) st) ↔
  Code.getReturn (part16_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%63"⟩) = prog
  unfold Code.part16
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_dropfelt]
  unfold part16_state_update part16_drops part16_state
  rfl

lemma part16_updates_opaque {st : State} : 
  Code.getReturn (part15_state_update st) ↔
  Code.getReturn (part16_state_update (part15_drops (part15_state st))) := by
  simp [part15_state_update, part16_wp]

lemma part16_cumulative_wp {in0 in1 in2 in3 data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17: Felt} :
  Code.run (start_state ([in0, in1, in2, in3]) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17])) ↔
  Code.getReturn
      (part16_state_update
        ((((({
                    buffers :=
                      ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                          [[some data0, some data1, some data2, some data3, some data4, some data5, some data6,
                              some data7, some data8, some data9, some data10, some data11, some data12, some data13,
                              some data14, some data15, some data16, some data17]])[{ name := "in" : BufferVar }] ←ₘ
                        [[some in0, some in1, some in2, some in3]],
                    bufferWidths :=
                      ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                          (18 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                        (4 : ℕ),
                    cycle := (0 : ℕ), felts := Map.empty, isFailed := False, props := Map.empty,
                    vars :=
                      [{ name := "in" : BufferVar },
                        { name := "data" : BufferVar }] }[props][{ name := "%6" : PropVar }] ←
                  True)[props][{ name := "%28" : PropVar }] ←
                in3 -
                    ((data10 * (64 : Felt) + (data1 * (16 : Felt) + data9 * (8 : Felt) + data8 * (4 : Felt) + data0)) *
                        (2 : Felt) +
                      data13) =
                  (0 : Felt))[props][{ name := "%43" : PropVar }] ←
              (in3 -
                    ((data10 * (64 : Felt) + (data1 * (16 : Felt) + data9 * (8 : Felt) + data8 * (4 : Felt) + data0)) *
                        (2 : Felt) +
                      data13) =
                  (0 : Felt) ∧
                in2 - ((data12 * (8 : Felt) + data2 * (2 : Felt) + data11) * (16 : Felt) + data4 * (4 : Felt) + data3) =
                  (0 : Felt)))[props][{ name := "%58" : PropVar }] ←
            ((in3 -
                    ((data10 * (64 : Felt) + (data1 * (16 : Felt) + data9 * (8 : Felt) + data8 * (4 : Felt) + data0)) *
                        (2 : Felt) +
                      data13) =
                  (0 : Felt) ∧
                in2 - ((data12 * (8 : Felt) + data2 * (2 : Felt) + data11) * (16 : Felt) + data4 * (4 : Felt) + data3) =
                  (0 : Felt)) ∧
              in1 - (data14 * (128 : Felt) + (data15 * (4 : Felt) + data5) * (16 : Felt) + data7 * (4 : Felt) + data6) =
                (0 : Felt)))[felts][{ name := "%63" : FeltVar }] ←
          in0 - (data16 * (128 : Felt) + data17)))  := by
    rewrite [part15_cumulative_wp]
    rewrite [part16_updates_opaque]
    unfold part15_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part15_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are statements after an if
    try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths, State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

lemma closed_form {in0 in1 in2 in3 data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17: Felt} :
  Code.run (start_state ([in0, in1, in2, in3]) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17])) ↔
   ((in3 -
              ((data10 * (64 : Felt) + (data1 * (16 : Felt) + data9 * (8 : Felt) + data8 * (4 : Felt) + data0)) *
                  (2 : Felt) +
                data13) =
            (0 : Felt) ∧
          in2 - ((data12 * (8 : Felt) + data2 * (2 : Felt) + data11) * (16 : Felt) + data4 * (4 : Felt) + data3) =
            (0 : Felt)) ∧
        in1 - (data14 * (128 : Felt) + (data15 * (4 : Felt) + data5) * (16 : Felt) + data7 * (4 : Felt) + data6) =
          (0 : Felt)) ∧
      in0 - (data16 * (128 : Felt) + data17) = (0 : Felt)  := by
    rewrite [part16_cumulative_wp]
    unfold part16_state_update
    unfold part16_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part16_drops
    -- 1 drop
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are statements after an if
    try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths, State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]
    unfold Code.getReturn
    simp only
    simp only [Code.getReturn, State.constraintsInVar, State.updateProps_props_get_wobbly, Option.getD_some]
end Risc0.ComputeDecode.Constraints.WP