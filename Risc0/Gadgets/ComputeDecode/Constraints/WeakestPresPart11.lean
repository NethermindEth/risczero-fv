import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart10

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part11 on st
def part11_state (st: State) : State := 
  
        ((((st["%44"] ←ₛ getImpl st { name := "data" } 0 6)["%45"] ←ₛ
              getImpl st { name := "data" } 0 7)[felts][{ name := "%46" }] ←
            Option.get! (State.felts (st["%45"] ←ₛ getImpl st { name := "data" } 0 7) { name := "%45" }) *
              Option.get! (State.felts st { name := "%4" }))["%47"] ←ₛ
          getImpl st { name := "data" } 0 5) 

-- Run the whole program by using part11_state rather than Code.part11
def part11_state_update (st: State): State :=
  Γ (part11_state st) ⟦Code.part12; Code.part13; Code.part14; Code.part15; Code.part16⟧

-- Prove that substituting part11_state for Code.part11 produces the same result
lemma part11_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) st) ↔
  Code.getReturn (part11_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) = prog
  unfold Code.part11
  MLIR
  unfold part11_state_update part11_state
  rewrite [←eq]
  rfl

lemma part11_updates_opaque {st : State} : 
  Code.getReturn (part10_state_update st) ↔
  Code.getReturn (part11_state_update (part10_state st)) := by
  simp [part10_state_update, part11_wp]

end Risc0.ComputeDecode.Constraints.WP