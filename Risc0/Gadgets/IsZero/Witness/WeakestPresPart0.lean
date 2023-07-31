import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.IsZero.Witness.CodeDrops

namespace Risc0.IsZero.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part0 on st
def part0_state (st: State) : State :=
  
        ((State.set!
            ((st["%1"] ←ₛ
                getImpl st { name := "in" : BufferVar } (0 : Back) (0 : ℕ))[felts][{ name := "%4" : FeltVar }] ←
              if
                  Option.get!
                      (State.felts (st["%1"] ←ₛ getImpl st { name := "in" : BufferVar } (0 : Back) (0 : ℕ))
                        { name := "%1" : FeltVar }) =
                    (0 : Felt) then
                (1 : Felt)
              else (0 : Felt))
            { name := "data" : BufferVar } (0 : ℕ)
            (if
                Option.get!
                    (State.felts (st["%1"] ←ₛ getImpl st { name := "in" : BufferVar } (0 : Back) (0 : ℕ))
                      { name := "%1" : FeltVar }) =
                  (0 : Felt) then
              (1 : Felt)
            else (0 : Felt)))[felts][{ name := "%5" : FeltVar }] ←
          if
              Option.get!
                  (st["%1"] ←ₛ
                        getImpl st { name := "in" : BufferVar } (0 : Back) (0 : ℕ)).felts[{ name := "%1" : FeltVar }] =
                (0 : Felt) then
            (0 : Felt)
          else
            (Option.get!
                (st["%1"] ←ₛ
                      getImpl st { name := "in" : BufferVar } (0 : Back)
                        (0 : ℕ)).felts[{ name := "%1" : FeltVar }])⁻¹) 

def part0_drops (st: State) : State :=
  st

-- Run the whole program by using part0_state rather than Code.part0
def part0_state_update (st: State): State :=
  Γ (part0_drops (part0_state st)) ⟦Code.part1;Code.part2;dropfelt ⟨"%1"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%6"⟩⟧

-- Prove that substituting part0_state for Code.part0 produces the same result
lemma part0_wp {st : State} {data0 data1 : Option Felt} :
  Code.getReturn (Γ st ⟦Code.part0;Code.part1;Code.part2;dropfelt ⟨"%1"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%6"⟩⟧) ([data0, data1]) ↔
  Code.getReturn (part0_state_update st) ([data0, data1]) := by
  generalize eq : (Code.part1;Code.part2;dropfelt ⟨"%1"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%6"⟩) = prog
  unfold Code.part0
  MLIR
  rewrite [←eq]
  
  unfold part0_state_update part0_drops part0_state
  rfl

set_option maxRecDepth 10000000 in
lemma part0_cumulative_wp {in0: Felt} {data0 data1: Option Felt} :
  Code.run (start_state ([in0])) ([data0, data1]) ↔
  Code.getReturn
      (part0_state_update
        {
          buffers :=
            Map.fromList
              [({ name := "in" : BufferVar }, [[some in0]]), ({ name := "data" : BufferVar }, [[none, none]])],
          bufferWidths :=
            Map.fromList [({ name := "in" : BufferVar }, (1 : ℕ)), ({ name := "data" : BufferVar }, (2 : ℕ))],
          cycle := (0 : ℕ), felts := Map.empty, isFailed := false = true, props := Map.empty,
          vars := [{ name := "in" : BufferVar }, { name := "data" : BufferVar }] })
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

end Risc0.IsZero.Witness.WP