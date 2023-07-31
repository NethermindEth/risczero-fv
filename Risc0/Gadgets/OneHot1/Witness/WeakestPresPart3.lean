import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot1.Witness.Code
import Risc0.Gadgets.OneHot1.Witness.WeakestPresPart2

namespace Risc0.OneHot1.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part3 on st
def part3_state (st: State) : State :=
   (withEqZero (Option.get! st.felts[{ name := "%7" : FeltVar }]!) st) 

def part3_drops (st: State) : State :=
  State.dropFelts (st) ⟨"%7"⟩

-- Run the program from part3 onwards by using part3_state rather than Code.part3
def part3_state_update (st: State): State :=
  part3_drops (part3_state st)

-- Prove that substituting part3_state for Code.part3 produces the same result
lemma part3_wp {st : State} {data0 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part3;dropfelt ⟨"%7"⟩) st) ([data0]) ↔
  Code.getReturn (part3_state_update st) ([data0]) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%7"⟩) = prog
  unfold Code.part3
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_dropfelt]
  unfold part3_state_update part3_drops part3_state
  rfl

lemma part3_updates_opaque {st : State} : 
  Code.getReturn (part2_state_update st) ([data0]) ↔
  Code.getReturn (part3_state_update (part2_drops (part2_state st))) ([data0]) := by
  simp [part2_state_update, part3_wp]

set_option maxRecDepth 10000000 in
lemma part3_cumulative_wp {code0: Felt} {data0: Option Felt} :
  Code.run (start_state ([code0])) ([data0]) ↔
  Code.getReturn
      (part3_state_update
        ({
            buffers :=
              ((fun x => Map.empty x)[{ name := "code" : BufferVar }] ←ₘ
                  [[some code0]])[{ name := "data" : BufferVar }] ←ₘ
                [[some (if code0 = (0 : Felt) then (1 : Felt) else (0 : Felt))]],
            bufferWidths :=
              ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ (1 : ℕ))[{ name := "code" : BufferVar }] ←ₘ
                (1 : ℕ),
            cycle := (0 : ℕ), felts := Map.empty,
            isFailed :=
              ¬code0 = (0 : Felt) ∨
                ¬((code0 = (0 : Felt) → False) ∨
                    ((1 : Felt) - if code0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt)),
            props := Map.empty,
            vars :=
              [{ name := "code" : BufferVar }, { name := "data" : BufferVar }] }[felts][{ name := "%7" : FeltVar }] ←
          (if code0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) - (1 : Felt)))
      ([data0])  := by
    rewrite [part2_cumulative_wp]
    rewrite [part3_updates_opaque]
    unfold part2_state
    try simplify_get_hack
    MLIR_states_updates
    -- 1 withEqZero
    rewrite [withEqZero_def]
    MLIR_states_updates
    unfold part2_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are statements after an if
    try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

lemma closed_form {code0: Felt} :
  Code.run (start_state [code0]) ([data0]) ↔
   some (if code0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) = data0 ∧
      ¬((¬code0 = (0 : Felt) ∨
            ¬((code0 = (0 : Felt) → False) ∨
                ((1 : Felt) - if code0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt))) ∨
          ¬(if code0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) - (1 : Felt) = (0 : Felt))  := by
    rewrite [part3_cumulative_wp]
    unfold part3_state_update
    unfold part3_state
    try simplify_get_hack
    MLIR_states_updates
    -- 1 withEqZero
    rewrite [withEqZero_def]
    MLIR_states_updates
    unfold part3_drops
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
end Risc0.OneHot1.Witness.WP