import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot2.Constraints.Code
import Risc0.Gadgets.OneHot2.Constraints.WeakestPresPart2

namespace Risc0.OneHot2.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part3 on st
def part3_state (st: State) : State :=
  
        ((((st[props][{ name := "%12" : PropVar }] ←
                (Option.get! (State.props st { name := "%9" : PropVar }) ∧
                  Option.get! (State.felts st { name := "%11" : FeltVar }) =
                    (0 : Felt)))[felts][{ name := "%13" : FeltVar }] ←
              Option.get! (State.felts st { name := "%6" : FeltVar }) +
                Option.get! (State.felts st { name := "%3" : FeltVar }))[felts][{ name := "%14" : FeltVar }] ←
            Option.get! (State.felts st { name := "%6" : FeltVar }) +
                Option.get! (State.felts st { name := "%3" : FeltVar }) -
              Option.get! (State.felts st { name := "%0" : FeltVar }))[props][{ name := "%15" : PropVar }] ←
          ((Option.get! (State.props st { name := "%9" : PropVar }) ∧
              Option.get! (State.felts st { name := "%11" : FeltVar }) = (0 : Felt)) ∧
            Option.get! (State.felts st { name := "%6" : FeltVar }) +
                  Option.get! (State.felts st { name := "%3" : FeltVar }) -
                Option.get! (State.felts st { name := "%0" : FeltVar }) =
              (0 : Felt))) 

def part3_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%3"⟩) ⟨"%0"⟩) ⟨"%6"⟩) ⟨"%11"⟩) ⟨"%13"⟩) ⟨"%14"⟩

-- Run the program from part3 onwards by using part3_state rather than Code.part3
def part3_state_update (st: State): State :=
  part3_drops (part3_state st)

-- Prove that substituting part3_state for Code.part3 produces the same result
lemma part3_wp {st : State}:
  Code.getReturn (MLIR.runProgram (Code.part3;dropfelt ⟨"%3"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩) st) ↔
  Code.getReturn (part3_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%3"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩) = prog
  unfold Code.part3
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_dropfelt]
  unfold part3_state_update part3_drops part3_state
  rfl

lemma part3_updates_opaque {st : State} : 
  Code.getReturn (part2_state_update st) ↔
  Code.getReturn (part3_state_update (part2_drops (part2_state st))) := by
  simp [part2_state_update, part3_wp]

lemma part3_cumulative_wp {code0 data0 data1: Felt} :
  Code.run (start_state ([code0]) ([data0, data1])) ↔
  Code.getReturn
      (part3_state_update
        ((((((({
                        buffers :=
                          ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                              [[some data0, some data1]])[{ name := "code" : BufferVar }] ←ₘ
                            [[some code0]],
                        bufferWidths :=
                          ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                              (2 : ℕ))[{ name := "code" : BufferVar }] ←ₘ
                            (1 : ℕ),
                        cycle := (0 : ℕ), felts := Map.empty, isFailed := False, props := Map.empty,
                        vars :=
                          [{ name := "code" : BufferVar },
                            { name := "data" : BufferVar }] }[props][{ name := "%1" : PropVar }] ←
                      True)[felts][{ name := "%3" : FeltVar }] ←
                    data1)[props][{ name := "%5" : PropVar }] ←
                  data1 - code0 = (0 : Felt))[felts][{ name := "%0" : FeltVar }] ←
                (1 : Felt))[felts][{ name := "%6" : FeltVar }] ←
              data0)[props][{ name := "%9" : PropVar }] ←
            (data1 - code0 = (0 : Felt) ∧
              (data0 = (0 : Felt) ∨ (1 : Felt) - data0 = (0 : Felt))))[felts][{ name := "%11" : FeltVar }] ←
          data1 * ((1 : Felt) - data1)))  := by
    rewrite [part2_cumulative_wp]
    rewrite [part3_updates_opaque]
    unfold part2_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part2_drops
    -- 3 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are statements after an if
    try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

lemma closed_form {code0 data0 data1: Felt} :
  Code.run (start_state ([code0]) ([data0, data1])) ↔
   ((data1 - code0 = (0 : Felt) ∧ (data0 = (0 : Felt) ∨ (1 : Felt) - data0 = (0 : Felt))) ∧
        (data1 = (0 : Felt) ∨ (1 : Felt) - data1 = (0 : Felt))) ∧
      data0 + data1 - (1 : Felt) = (0 : Felt)  := by
    rewrite [part3_cumulative_wp]
    unfold part3_state_update
    unfold part3_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part3_drops
    -- 6 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
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
    simp only [Code.getReturn, State.constraintsInVar, State.updateProps_props_get_wobbly, Option.getD_some]
end Risc0.OneHot2.Constraints.WP