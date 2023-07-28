import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot2.Witness.Code
import Risc0.Gadgets.OneHot2.Witness.WeakestPresPart1

namespace Risc0.OneHot2.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part2 on st
def part2_state (st: State) : State :=
  
        (((withEqZero
              (Option.get! (State.felts st { name := "%3" : FeltVar }) -
                Option.get! (State.felts st { name := "%2" : FeltVar }))
              (st[felts][{ name := "%4" : FeltVar }] ←
                Option.get! (State.felts st { name := "%3" : FeltVar }) -
                  Option.get! (State.felts st { name := "%2" : FeltVar })))["%5"] ←ₛ
            getImpl st { name := "data" : BufferVar } (0 : Back) (0 : ℕ))[felts][{ name := "%6" : FeltVar }] ←
          Option.get! (State.felts st { name := "%0" : FeltVar }) -
            Option.get!
              (State.felts
                ((withEqZero
                    (Option.get! (State.felts st { name := "%3" : FeltVar }) -
                      Option.get! (State.felts st { name := "%2" : FeltVar }))
                    (st[felts][{ name := "%4" : FeltVar }] ←
                      Option.get! (State.felts st { name := "%3" : FeltVar }) -
                        Option.get! (State.felts st { name := "%2" : FeltVar })))["%5"] ←ₛ
                  getImpl st { name := "data" : BufferVar } (0 : Back) (0 : ℕ))
                { name := "%5" : FeltVar })) 

def part2_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (st) ⟨"%2"⟩) ⟨"%4"⟩

-- Run the program from part2 onwards by using part2_state rather than Code.part2
def part2_state_update (st: State): State :=
  Γ (part2_drops (part2_state st)) ⟦Code.part3;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;Code.part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;Code.part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧

-- Prove that substituting part2_state for Code.part2 produces the same result
lemma part2_wp {st : State} {data0 data1 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;Code.part3;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;Code.part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;Code.part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩) st) ([data0, data1]) ↔
  Code.getReturn (part2_state_update st) ([data0, data1]) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;Code.part3;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;Code.part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;Code.part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩) = prog
  unfold Code.part2
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part2_state_update part2_drops part2_state
  rfl

lemma part2_updates_opaque {st : State} : 
  Code.getReturn (part1_state_update st) ([data0, data1]) ↔
  Code.getReturn (part2_state_update (part1_drops (part1_state st))) ([data0, data1]) := by
  simp [part1_state_update, part2_wp]

lemma part2_cumulative_wp {code0: Felt} {data0 data1: Option Felt} :
  Code.run (start_state ([code0])) ([data0, data1]) ↔
  Code.getReturn
      (part2_state_update
        ({
            buffers :=
              (Map.empty[{ name := "code" : BufferVar }] ←ₘ [[some code0]])[{ name := "data" : BufferVar }] ←ₘ
                [[some (if code0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                    some (if code0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))]],
            bufferWidths :=
              ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ (2 : ℕ))[{ name := "code" : BufferVar }] ←ₘ
                (1 : ℕ),
            cycle := (0 : ℕ),
            felts := (Map.empty[{ name := "%2" : FeltVar }] ←ₘ code0)[{ name := "%0" : FeltVar }] ←ₘ (1 : Felt),
            isFailed := False, props := Map.empty,
            vars :=
              [{ name := "code" : BufferVar }, { name := "data" : BufferVar }] }[felts][{ name := "%3" : FeltVar }] ←
          if code0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)))
      ([data0, data1])  := by
    rewrite [part1_cumulative_wp]
    rewrite [part2_updates_opaque]
    unfold part1_state
    try simplify_get_hack
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part1_drops
    -- 2 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 1 set
    rewrite [Map.drop_of_updates]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.OneHot2.Witness.WP