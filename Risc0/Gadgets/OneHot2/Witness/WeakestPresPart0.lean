import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot2.Witness.CodeDrops

namespace Risc0.OneHot2.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part0 on st
def part0_state (st: State) : State :=
  
        ((State.set!
            ((st["%2"] ←ₛ
                getImpl st { name := "code" : BufferVar } (0 : Back) (0 : ℕ))[felts][{ name := "%12" : FeltVar }] ←
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
            else (0 : Felt)))[felts][{ name := "%0" : FeltVar }] ←
          (1 : Felt)) 

def part0_drops (st: State) : State :=
  State.dropFelts (st) ⟨"%12"⟩

-- Run the whole program by using part0_state rather than Code.part0
def part0_state_update (st: State): State :=
  Γ (part0_drops (part0_state st)) ⟦Code.part1;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;Code.part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;Code.part3;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;Code.part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;Code.part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧

-- Prove that substituting part0_state for Code.part0 produces the same result
lemma part0_wp {st : State} {data0 data1 : Option Felt} :
  Code.getReturn (Γ st ⟦Code.part0;dropfelt ⟨"%12"⟩;Code.part1;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;Code.part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;Code.part3;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;Code.part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;Code.part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧) ([data0, data1]) ↔
  Code.getReturn (part0_state_update st) ([data0, data1]) := by
  generalize eq : (dropfelt ⟨"%12"⟩;Code.part1;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;Code.part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;Code.part3;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;Code.part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;Code.part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩) = prog
  unfold Code.part0
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part0_state_update part0_drops part0_state
  rfl

lemma part0_cumulative_wp {code0: Felt} {data0 data1: Option Felt} :
  Code.run (start_state ([code0])) ([data0, data1]) ↔
  Code.getReturn
      (part0_state_update
        {
          buffers :=
            Map.fromList
              [({ name := "code" : BufferVar }, [[some code0]]), ({ name := "data" : BufferVar }, [[none, none]])],
          bufferWidths :=
            Map.fromList [({ name := "code" : BufferVar }, (1 : ℕ)), ({ name := "data" : BufferVar }, (2 : ℕ))],
          cycle := (0 : ℕ), felts := Map.empty, isFailed := false = true, props := Map.empty,
          vars := [{ name := "code" : BufferVar }, { name := "data" : BufferVar }] })
      ([data0, data1])  := by
    unfold Code.run start_state
    rewrite [Code.optimised_behaviour_full]
    unfold MLIR.runProgram
    rewrite [←Code.parts_combine]
    unfold Code.parts_combined
    rewrite [←Code.getReturn_ignores_drops]
    rewrite [←Code.behaviour_with_drops]
    rewrite [part0_wp]
    rfl

end Risc0.OneHot2.Witness.WP