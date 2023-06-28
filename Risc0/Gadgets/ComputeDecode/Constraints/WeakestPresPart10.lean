import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart9

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part10 on st
def part10_state (st: State) : State := 
  
        ((((st[felts][{ name := "%40" }] ←
                Option.get! (State.felts st { name := "%39" }) +
                  Option.get! (State.felts st { name := "%31" }))[felts][{ name := "%41" }] ←
              Option.get! (State.felts st { name := "%39" }) + Option.get! (State.felts st { name := "%31" }) +
                Option.get! (State.felts st { name := "%29" }))[felts][{ name := "%42" }] ←
            Option.get! (State.felts st { name := "%9" }) -
              (Option.get! (State.felts st { name := "%39" }) + Option.get! (State.felts st { name := "%31" }) +
                Option.get! (State.felts st { name := "%29" })))[props][{ name := "%43" }] ←
          (Option.get! (State.props st { name := "%28" }) ∧
            Option.get! (State.felts st { name := "%9" }) -
                (Option.get! (State.felts st { name := "%39" }) + Option.get! (State.felts st { name := "%31" }) +
                  Option.get! (State.felts st { name := "%29" })) =
              0)) 

-- Run the whole program by using part10_state rather than Code.part10
def part10_state_update (st: State): State :=
  Γ (part10_state st) ⟦Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16⟧

-- Prove that substituting part10_state for Code.part10 produces the same result
lemma part10_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) st) ↔
  Code.getReturn (part10_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) = prog
  unfold Code.part10
  MLIR
  unfold part10_state_update part10_state
  rewrite [←eq]
  rfl

lemma part10_updates_opaque {st : State} : 
  Code.getReturn (part9_state_update st) ↔
  Code.getReturn (part10_state_update (part9_state st)) := by
  simp [part9_state_update, part10_wp]

end Risc0.ComputeDecode.Constraints.WP