import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot2.Constraints.CodeDrops

namespace Risc0.OneHot2.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part0 on st
def part0_state (st: State) : State :=
  
        ((((st[props][{ name := "%1" : PropVar }] ← True)["%2"] ←ₛ
              getImpl st { name := "code" : BufferVar } (0 : Back) (0 : ℕ))["%3"] ←ₛ
            getImpl st { name := "data" : BufferVar } (0 : Back) (1 : ℕ))[felts][{ name := "%4" : FeltVar }] ←
          Option.get!
              (State.felts
                ((st[props][{ name := "%1" : PropVar }] ← True)["%3"] ←ₛ
                  getImpl st { name := "data" : BufferVar } (0 : Back) (1 : ℕ))
                { name := "%3" : FeltVar }) -
            Option.get!
              (State.felts
                ((st[props][{ name := "%1" : PropVar }] ← True)["%2"] ←ₛ
                  getImpl st { name := "code" : BufferVar } (0 : Back) (0 : ℕ))
                { name := "%2" : FeltVar })) 

def part0_drops (st: State) : State :=
  State.dropFelts (st) ⟨"%2"⟩

-- Run the whole program by using part0_state rather than Code.part0
def part0_state_update (st: State): State :=
  Γ (part0_drops (part0_state st)) ⟦Code.part1;dropfelt ⟨"%4"⟩;Code.part2;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%10"⟩;Code.part3;dropfelt ⟨"%3"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩⟧

-- Prove that substituting part0_state for Code.part0 produces the same result
lemma part0_wp {st : State} :
  Code.getReturn (Γ st ⟦Code.part0;dropfelt ⟨"%2"⟩;Code.part1;dropfelt ⟨"%4"⟩;Code.part2;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%10"⟩;Code.part3;dropfelt ⟨"%3"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩⟧)↔
  Code.getReturn (part0_state_update st) := by
  generalize eq : (dropfelt ⟨"%2"⟩;Code.part1;dropfelt ⟨"%4"⟩;Code.part2;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%10"⟩;Code.part3;dropfelt ⟨"%3"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩) = prog
  unfold Code.part0
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part0_state_update part0_drops part0_state
  rfl

lemma part0_cumulative_wp {code0 data0 data1: Felt}:
  Code.run (start_state ([code0]) ([data0, data1])) ↔
  Code.getReturn
      (part0_state_update
        {
          buffers :=
            Map.fromList
              [({ name := "code" : BufferVar }, [[some code0]]),
                ({ name := "data" : BufferVar }, [[some data0, some data1]])],
          bufferWidths :=
            Map.fromList [({ name := "code" : BufferVar }, (1 : ℕ)), ({ name := "data" : BufferVar }, (2 : ℕ))],
          constraints := [], cycle := (0 : ℕ), felts := Map.empty, isFailed := false, props := Map.empty,
          vars := [{ name := "code" : BufferVar }, { name := "data" : BufferVar }] })  := by
    unfold Code.run start_state
    rewrite [Code.optimised_behaviour_full]
    unfold MLIR.runProgram
    rewrite [←Code.parts_combine]
    unfold Code.parts_combined
    rewrite [←Code.getReturn_ignores_drops]
    rewrite [←Code.behaviour_with_drops]
    rewrite [part0_wp]
    rfl

end Risc0.OneHot2.Constraints.WP