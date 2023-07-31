import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot2.Witness.Code
import Risc0.Gadgets.OneHot2.Witness.WeakestPresPart4

namespace Risc0.OneHot2.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part5 on st
def part5_state (st: State) : State :=
   (withEqZero (Option.get! st.felts[{ name := "%11" : FeltVar }]!) st) 

def part5_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (st) ⟨"%11"⟩) ⟨"%1"⟩

-- Run the program from part5 onwards by using part5_state rather than Code.part5
def part5_state_update (st: State): State :=
  part5_drops (part5_state st)

-- Prove that substituting part5_state for Code.part5 produces the same result
lemma part5_wp {st : State} {y0 y1 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩) st) = [y0, y1] ↔
  Code.getReturn (part5_state_update st) = [y0, y1] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩) = prog
  unfold Code.part5
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_dropfelt]
  unfold part5_state_update part5_drops part5_state
  rfl

lemma part5_updates_opaque {st : State} : 
  Code.getReturn (part4_state_update st) = [y0, y1] ↔
  Code.getReturn (part5_state_update (part4_drops (part4_state st))) = [y0, y1] := by
  simp [part4_state_update, part5_wp]

set_option maxRecDepth 10000000 in
lemma part5_cumulative_wp {x0: Felt} :
  Code.run (start_state [x0]) = [y0,y1] ↔
  Code.getReturn
        (part5_state_update
          (({
                buffers :=
                  ((fun x => Map.empty x)[{ name := "code" : BufferVar }] ←ₘ
                      [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                    [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                        some (if x0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))]],
                bufferWidths :=
                  ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ (2 : ℕ))[{ name := "code" : BufferVar }] ←ₘ
                    (1 : ℕ),
                constraints :=
                  [(x0 - (1 : Felt) = (0 : Felt) → False) ∨
                      ((1 : Felt) - if x0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                    (x0 = (0 : Felt) → False) ∨
                      ((1 : Felt) - if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                    (if x0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) - x0 = (0 : Felt)],
                cycle := (0 : ℕ), felts := Map.empty, isFailed := false, props := Map.empty,
                vars :=
                  [{ name := "code" : BufferVar },
                    { name := "data" : BufferVar }] }[felts][{ name := "%11" : FeltVar }] ←
              ((if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                  if x0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) -
                (1 : Felt))[felts][{ name := "%1" : FeltVar }] ←
            (0 : Felt))) =
      [y0, y1]  := by
    rewrite [part4_cumulative_wp]
    rewrite [part5_updates_opaque]
    unfold part4_state
    try simplify_get_hack
    MLIR_states_updates
    -- 1 withEqZero
    rewrite [withEqZero_def]
    MLIR_states_updates
    unfold part4_drops
    -- 5 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are statements after an if
    try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.constraints_if_eq_if_constraints,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

lemma closed_form {x0: Felt} :
  Code.run (start_state [x0]) = [y0,y1] ↔
   some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y0 ∧
      some (if x0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y1  := by
    rewrite [part5_cumulative_wp]
    unfold part5_state_update
    unfold part5_state
    try simplify_get_hack
    MLIR_states_updates
    -- 1 withEqZero
    rewrite [withEqZero_def]
    MLIR_states_updates
    unfold part5_drops
    -- 2 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are statements after an if
    try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.constraints_if_eq_if_constraints,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]
    unfold Code.getReturn
    simp only
    simp [Map.update_get_wobbly, List.getLast!]
end Risc0.OneHot2.Witness.WP