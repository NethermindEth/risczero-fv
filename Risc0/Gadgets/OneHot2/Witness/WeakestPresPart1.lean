import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot2.Witness.Code
import Risc0.Gadgets.OneHot2.Witness.WeakestPresPart0

namespace Risc0.OneHot2.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part1 on st
def part1_state (st: State) : State :=
  
          ((State.set!
              ((st[felts][{ name := "%13" : FeltVar }] ←
                  Option.get! (State.felts st { name := "%2" : FeltVar }) -
                    Option.get! (State.felts st { name := "%0" : FeltVar }))[felts][{ name := "%14" : FeltVar }] ←
                if
                    Option.get! (State.felts st { name := "%2" : FeltVar }) -
                        Option.get! (State.felts st { name := "%0" : FeltVar }) =
                      (0 : Felt) then
                  (1 : Felt)
                else (0 : Felt))
              { name := "data" : BufferVar } (1 : ℕ)
              (if
                  Option.get! (State.felts st { name := "%2" : FeltVar }) -
                      Option.get! (State.felts st { name := "%0" : FeltVar }) =
                    (0 : Felt) then
                (1 : Felt)
              else (0 : Felt)))["%3"] ←ₛ
            getImpl
              (State.set!
                ((st[felts][{ name := "%13" : FeltVar }] ←
                    Option.get! (State.felts st { name := "%2" : FeltVar }) -
                      Option.get! (State.felts st { name := "%0" : FeltVar }))[felts][{ name := "%14" : FeltVar }] ←
                  if
                      Option.get! (State.felts st { name := "%2" : FeltVar }) -
                          Option.get! (State.felts st { name := "%0" : FeltVar }) =
                        (0 : Felt) then
                    (1 : Felt)
                  else (0 : Felt))
                { name := "data" : BufferVar } (1 : ℕ)
                (if
                    Option.get! (State.felts st { name := "%2" : FeltVar }) -
                        Option.get! (State.felts st { name := "%0" : FeltVar }) =
                      (0 : Felt) then
                  (1 : Felt)
                else (0 : Felt)))
              { name := "data" : BufferVar } (0 : Back) (1 : ℕ)) 

def part1_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (st) ⟨"%13"⟩) ⟨"%14"⟩

-- Run the program from part1 onwards by using part1_state rather than Code.part1
def part1_state_update (st: State): State :=
  Γ (part1_drops (part1_state st)) ⟦Code.part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;Code.part3;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;Code.part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;Code.part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧

-- Prove that substituting part1_state for Code.part1 produces the same result
lemma part1_wp {st : State} {y0 y1 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part1;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;Code.part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;Code.part3;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;Code.part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;Code.part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩) st) = [y0, y1] ↔
  Code.getReturn (part1_state_update st) = [y0, y1] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;Code.part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;Code.part3;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;Code.part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;Code.part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩) = prog
  unfold Code.part1
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part1_state_update part1_drops part1_state
  rfl

lemma part1_updates_opaque {st : State} : 
  Code.getReturn (part0_state_update st) = [y0, y1] ↔
  Code.getReturn (part1_state_update (part0_drops (part0_state st))) = [y0, y1] := by
  simp [part0_state_update, part1_wp]

lemma part1_cumulative_wp {x0: Felt} :
  Code.run (start_state [x0]) = [y0,y1] ↔
  Code.getReturn
        (part1_state_update
          ({
              buffers :=
                (Map.empty[{ name := "code" : BufferVar }] ←ₘ [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                  [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)), none]],
              bufferWidths :=
                ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ (2 : ℕ))[{ name := "code" : BufferVar }] ←ₘ
                  (1 : ℕ),
              constraints := [], cycle := (0 : ℕ), felts := Map.empty[{ name := "%2" : FeltVar }] ←ₘ x0,
              isFailed := false, props := Map.empty,
              vars :=
                [{ name := "code" : BufferVar }, { name := "data" : BufferVar }] }[felts][{ name := "%0" : FeltVar }] ←
            (1 : Felt))) =
      [y0, y1]  := by
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

end Risc0.OneHot2.Witness.WP