import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot1.Witness.Code
import Risc0.Gadgets.OneHot1.Witness.WeakestPresPart0

namespace Risc0.OneHot1.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part1 on st
def part1_state (st: State) : State :=
  
          (((withEqZero
                (Option.get! (State.felts st { name := "%1" : FeltVar }) -
                  Option.get! (State.felts st { name := "%2" : FeltVar }))
                (st[felts][{ name := "%3" : FeltVar }] ←
                  Option.get! (State.felts st { name := "%1" : FeltVar }) -
                    Option.get! (State.felts st { name := "%2" : FeltVar })))[felts][{ name := "%0" : FeltVar }] ←
              (1 : Felt))["%4"] ←ₛ
            getImpl st { name := "data" : BufferVar } (0 : Back) (0 : ℕ)) 

def part1_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%2"⟩) ⟨"%1"⟩) ⟨"%3"⟩

-- Run the program from part1 onwards by using part1_state rather than Code.part1
def part1_state_update (st: State): State :=
  Γ (part1_drops (part1_state st)) ⟦Code.part2;dropfelt ⟨"%0"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%6"⟩;Code.part3;dropfelt ⟨"%7"⟩⟧

-- Prove that substituting part1_state for Code.part1 produces the same result
lemma part1_wp {st : State} {y0 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part1;dropfelt ⟨"%2"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%3"⟩;Code.part2;dropfelt ⟨"%0"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%6"⟩;Code.part3;dropfelt ⟨"%7"⟩) st) = [y0] ↔
  Code.getReturn (part1_state_update st) = [y0] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%2"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%3"⟩;Code.part2;dropfelt ⟨"%0"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%6"⟩;Code.part3;dropfelt ⟨"%7"⟩) = prog
  unfold Code.part1
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part1_state_update part1_drops part1_state
  rfl

lemma part1_updates_opaque {st : State} : 
  Code.getReturn (part0_state_update st) = [y0] ↔
  Code.getReturn (part1_state_update (part0_drops (part0_state st))) = [y0] := by
  simp [part0_state_update, part1_wp]

lemma part1_cumulative_wp {x0: Felt} :
  Code.run (start_state [x0]) = [y0] ↔
  Code.getReturn
        (part1_state_update
          ({
              buffers :=
                (Map.empty[{ name := "code" : BufferVar }] ←ₘ [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                  [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt))]],
              bufferWidths :=
                ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ (1 : ℕ))[{ name := "code" : BufferVar }] ←ₘ
                  (1 : ℕ),
              constraints := [], cycle := (0 : ℕ), felts := Map.empty[{ name := "%2" : FeltVar }] ←ₘ x0,
              isFailed := false, props := Map.empty,
              vars :=
                [{ name := "code" : BufferVar }, { name := "data" : BufferVar }] }[felts][{ name := "%1" : FeltVar }] ←
            (0 : Felt))) =
      [y0]  := by
    rewrite [part0_cumulative_wp]
    rewrite [part1_updates_opaque]
    unfold part0_state
    try simplify_get_hack
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part0_drops
    -- 1 drop
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 1 set
    rewrite [Map.drop_of_updates]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

end Risc0.OneHot1.Witness.WP