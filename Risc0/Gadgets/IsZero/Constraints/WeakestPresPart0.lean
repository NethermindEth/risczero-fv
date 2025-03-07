import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.IsZero.Constraints.CodeDrops

namespace Risc0.IsZero.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part0 on st
def part0_state (st: State) : State :=
  
        ((((st[props][{ name := "%1" : PropVar }] ← True)["%2"] ←ₛ
              getImpl st { name := "in" : BufferVar } (0 : Back) (0 : ℕ))[props][{ name := "%4" : PropVar }] ←
            (Option.get!
                (State.props
                  ((st[props][{ name := "%1" : PropVar }] ← True)["%2"] ←ₛ
                    getImpl st { name := "in" : BufferVar } (0 : Back) (0 : ℕ))
                  { name := "%1" : PropVar }) ∧
              Option.get!
                  (State.felts
                    ((st[props][{ name := "%1" : PropVar }] ← True)["%2"] ←ₛ
                      getImpl st { name := "in" : BufferVar } (0 : Back) (0 : ℕ))
                    { name := "%2" : FeltVar }) =
                (0 : Felt)))["%3"] ←ₛ
          getImpl st { name := "data" : BufferVar } (0 : Back) (0 : ℕ)) 

def part0_drops (st: State) : State :=
  st

-- Run the whole program by using part0_state rather than Code.part0
def part0_state_update (st: State): State :=
  Γ (part0_drops (part0_state st)) ⟦Code.part1;dropfelt ⟨"%3"⟩;Code.part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%9"⟩⟧

-- Prove that substituting part0_state for Code.part0 produces the same result
lemma part0_wp {st : State} :
  Code.getReturn (Γ st ⟦Code.part0;Code.part1;dropfelt ⟨"%3"⟩;Code.part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%9"⟩⟧)↔
  Code.getReturn (part0_state_update st) := by
  generalize eq : (Code.part1;dropfelt ⟨"%3"⟩;Code.part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%9"⟩) = prog
  unfold Code.part0
  MLIR
  rewrite [←eq]
  
  unfold part0_state_update part0_drops part0_state
  rfl
lemma part0_cumulative_wp {in0 data0 data1: Felt}:
  Code.run (start_state ([in0]) ([data0, data1])) ↔
  Code.getReturn
      (part0_state_update
        {
          buffers :=
            Map.fromList
              [({ name := "in" : BufferVar }, [[some in0]]),
                ({ name := "data" : BufferVar }, [[some data0, some data1]])],
          bufferWidths :=
            Map.fromList [({ name := "in" : BufferVar }, (1 : ℕ)), ({ name := "data" : BufferVar }, (2 : ℕ))],
          cycle := (0 : ℕ), felts := Map.empty, isFailed := false = true, props := Map.empty,
          vars := [{ name := "in" : BufferVar }, { name := "data" : BufferVar }] })  := by
    unfold Code.run start_state
    rewrite [Code.optimised_behaviour_full]
    unfold MLIR.runProgram
    rewrite [←Code.parts_combine]
    unfold Code.parts_combined
    rewrite [←Code.getReturn_ignores_drops]
    rewrite [←Code.behaviour_with_drops]
    rewrite [part0_wp]
    rfl

end Risc0.IsZero.Constraints.WP