import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot2.Constraints.Code
import Risc0.Gadgets.OneHot2.Constraints.WeakestPresPart1

namespace Risc0.OneHot2.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part2 on st
def part2_state (st: State) : State :=
  
        ((((st[felts][{ name := "%8" : FeltVar }] ←
                Option.get! (State.felts st { name := "%6" : FeltVar }) *
                  Option.get! (State.felts st { name := "%7" : FeltVar }))[props][{ name := "%9" : PropVar }] ←
              (Option.get! (State.props st { name := "%5" : PropVar }) ∧
                (Option.get! (State.felts st { name := "%6" : FeltVar }) = (0 : Felt) ∨
                  Option.get! (State.felts st { name := "%7" : FeltVar }) =
                    (0 : Felt))))[felts][{ name := "%10" : FeltVar }] ←
            Option.get! (State.felts st { name := "%0" : FeltVar }) -
              Option.get! (State.felts st { name := "%3" : FeltVar }))[felts][{ name := "%11" : FeltVar }] ←
          Option.get! (State.felts st { name := "%3" : FeltVar }) *
            (Option.get! (State.felts st { name := "%0" : FeltVar }) -
              Option.get! (State.felts st { name := "%3" : FeltVar }))) 

def part2_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%7"⟩) ⟨"%8"⟩) ⟨"%10"⟩

-- Run the program from part2 onwards by using part2_state rather than Code.part2
def part2_state_update (st: State): State :=
  Γ (part2_drops (part2_state st)) ⟦Code.part3;dropfelt ⟨"%3"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩⟧

-- Prove that substituting part2_state for Code.part2 produces the same result
lemma part2_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part2;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%10"⟩;Code.part3;dropfelt ⟨"%3"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩) st) ↔
  Code.getReturn (part2_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%10"⟩;Code.part3;dropfelt ⟨"%3"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩) = prog
  unfold Code.part2
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part2_state_update part2_drops part2_state
  rfl

lemma part2_updates_opaque {st : State} : 
  Code.getReturn (part1_state_update st) ↔
  Code.getReturn (part2_state_update (part1_drops (part1_state st))) := by
  simp [part1_state_update, part2_wp]

set_option maxRecDepth 10000000 in
lemma part2_cumulative_wp {code0 data0 data1: Felt} :
  Code.run (start_state ([code0]) ([data0, data1])) ↔
  Code.getReturn
      (part2_state_update
        (((((({
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
            data0)[felts][{ name := "%7" : FeltVar }] ←
          (1 : Felt) - data0))  := by
    rewrite [part1_cumulative_wp]
    rewrite [part2_updates_opaque]
    unfold part1_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part1_drops
    -- 1 drop
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths, State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.OneHot2.Constraints.WP