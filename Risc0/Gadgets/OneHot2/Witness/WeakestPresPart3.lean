import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot2.Witness.Code
import Risc0.Gadgets.OneHot2.Witness.WeakestPresPart2

namespace Risc0.OneHot2.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part3 on st
def part3_state (st: State) : State :=
  
        (((withEqZero
              (Option.get! (State.felts st { name := "%5" : FeltVar }) *
                Option.get! (State.felts st { name := "%6" : FeltVar }))
              (st[felts][{ name := "%7" : FeltVar }] ←
                Option.get! (State.felts st { name := "%5" : FeltVar }) *
                  Option.get! (State.felts st { name := "%6" : FeltVar })))[felts][{ name := "%8" : FeltVar }] ←
            Option.get! (State.felts st { name := "%0" : FeltVar }) -
              Option.get! (State.felts st { name := "%3" : FeltVar }))[felts][{ name := "%9" : FeltVar }] ←
          Option.get! (State.felts st { name := "%3" : FeltVar }) *
            (Option.get! (State.felts st { name := "%0" : FeltVar }) -
              Option.get! (State.felts st { name := "%3" : FeltVar }))) 

def part3_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%6"⟩) ⟨"%7"⟩) ⟨"%8"⟩

-- Run the program from part3 onwards by using part3_state rather than Code.part3
def part3_state_update (st: State): State :=
  Γ (part3_drops (part3_state st)) ⟦Code.part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;Code.part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧

-- Prove that substituting part3_state for Code.part3 produces the same result
lemma part3_wp {st : State} {data0 data1 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part3;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;Code.part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;Code.part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩) st) ([data0, data1]) ↔
  Code.getReturn (part3_state_update st) ([data0, data1]) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;Code.part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;Code.part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩) = prog
  unfold Code.part3
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part3_state_update part3_drops part3_state
  rfl

lemma part3_updates_opaque {st : State} : 
  Code.getReturn (part2_state_update st) ([data0, data1]) ↔
  Code.getReturn (part3_state_update (part2_drops (part2_state st))) ([data0, data1]) := by
  simp [part2_state_update, part3_wp]

set_option maxRecDepth 10000000 in
lemma part3_cumulative_wp {code0: Felt} {data0 data1: Option Felt} :
  Code.run (start_state ([code0])) ([data0, data1]) ↔
  Code.getReturn
      (part3_state_update
        (({
              buffers :=
                ((fun x => Map.empty x)[{ name := "code" : BufferVar }] ←ₘ
                    [[some code0]])[{ name := "data" : BufferVar }] ←ₘ
                  [[some (if code0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if code0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))]],
              bufferWidths :=
                ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ (2 : ℕ))[{ name := "code" : BufferVar }] ←ₘ
                  (1 : ℕ),
              cycle := (0 : ℕ),
              felts :=
                (Map.empty[{ name := "%0" : FeltVar }] ←ₘ (1 : Felt))[{ name := "%3" : FeltVar }] ←ₘ
                  if code0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt),
              isFailed :=
                False ∨ ¬(if code0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) - code0 = (0 : Felt),
              props := Map.empty,
              vars :=
                [{ name := "code" : BufferVar }, { name := "data" : BufferVar }] }[felts][{ name := "%5" : FeltVar }] ←
            if code0 = (0 : Felt) then (1 : Felt) else (0 : Felt))[felts][{ name := "%6" : FeltVar }] ←
          (1 : Felt) - if code0 = (0 : Felt) then (1 : Felt) else (0 : Felt)))
      ([data0, data1])  := by
    rewrite [part2_cumulative_wp]
    rewrite [part3_updates_opaque]
    unfold part2_state
    try simplify_get_hack
    MLIR_states_updates
    -- 1 withEqZero
    rewrite [withEqZero_def]
    MLIR_states_updates
    unfold part2_drops
    -- 2 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.OneHot2.Witness.WP