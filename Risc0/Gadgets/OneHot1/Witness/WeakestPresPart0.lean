import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot1.Witness.CodeDrops

namespace Risc0.OneHot1.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part0 on st
def part0_state (st: State) : State :=
  
          ((State.set!
              ((st["%2"] ←ₛ
                  getImpl st { name := "code" : BufferVar } (0 : Back) (0 : ℕ))[felts][{ name := "%8" : FeltVar }] ←
                if
                    Option.get!
                        (State.felts (st["%2"] ←ₛ getImpl st { name := "code" : BufferVar } (0 : Back) (0 : ℕ))
                          { name := "%2" : FeltVar }) =
                      (0 : Felt) then
                  (1 : Felt)
                else (0 : Felt))
              { name := "data" : BufferVar } (0 : ℕ)
              (if
                  Option.get!
                      (State.felts (st["%2"] ←ₛ getImpl st { name := "code" : BufferVar } (0 : Back) (0 : ℕ))
                        { name := "%2" : FeltVar }) =
                    (0 : Felt) then
                (1 : Felt)
              else (0 : Felt)))[felts][{ name := "%1" : FeltVar }] ←
            (0 : Felt)) 

def part0_drops (st: State) : State :=
  State.dropFelts (st) ⟨"%8"⟩

-- Run the whole program by using part0_state rather than Code.part0
def part0_state_update (st: State): State :=
  Γ (part0_drops (part0_state st)) ⟦Code.part1;dropfelt ⟨"%2"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%3"⟩;Code.part2;dropfelt ⟨"%0"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%6"⟩;Code.part3;dropfelt ⟨"%7"⟩⟧

-- Prove that substituting part0_state for Code.part0 produces the same result
lemma part0_wp {st : State} {y0 : Option Felt} :
  Code.getReturn (Γ st ⟦Code.part0;dropfelt ⟨"%8"⟩;Code.part1;dropfelt ⟨"%2"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%3"⟩;Code.part2;dropfelt ⟨"%0"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%6"⟩;Code.part3;dropfelt ⟨"%7"⟩⟧) = [y0] ↔
  Code.getReturn (part0_state_update st) = [y0] := by
  generalize eq : (dropfelt ⟨"%8"⟩;Code.part1;dropfelt ⟨"%2"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%3"⟩;Code.part2;dropfelt ⟨"%0"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%6"⟩;Code.part3;dropfelt ⟨"%7"⟩) = prog
  unfold Code.part0
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part0_state_update part0_drops part0_state
  rfl

lemma part0_cumulative_wp {x0: Felt} :
  Code.run (start_state [x0]) = [y0] ↔
  Code.getReturn
        (part0_state_update
          {
            buffers :=
              Map.fromList [({ name := "code" : BufferVar }, [[some x0]]), ({ name := "data" : BufferVar }, [[none]])],
            bufferWidths :=
              Map.fromList [({ name := "code" : BufferVar }, (1 : ℕ)), ({ name := "data" : BufferVar }, (1 : ℕ))],
            constraints := [], cycle := (0 : ℕ), felts := Map.empty, isFailed := false, props := Map.empty,
            vars := [{ name := "code" : BufferVar }, { name := "data" : BufferVar }] }) =
      [y0]  := by
    unfold Code.run start_state
    rewrite [Code.optimised_behaviour_full]
    unfold MLIR.runProgram
    rewrite [←Code.parts_combine]
    unfold Code.parts_combined
    rewrite [←Code.getReturn_ignores_drops]
    rewrite [←Code.behaviour_with_drops]
    rewrite [part0_wp]
    rfl

end Risc0.OneHot1.Witness.WP