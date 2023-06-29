import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart23

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part24 on st
def part24_state (st: State) : State := 
  
        ((((st[props][{ name := "%96" }] ←
                (Option.get! (State.props st { name := "%92" }) ∧
                  Option.get! (State.felts st { name := "%95" }) = 0))[felts][{ name := "%97" }] ←
              Option.get! (State.felts st { name := "%93" }) +
                Option.get! (State.felts st { name := "%28" }))[felts][{ name := "%98" }] ←
            Option.get! (State.felts st { name := "%0" }) -
              Option.get! (State.felts st { name := "%31" }))[felts][{ name := "%99" }] ←
          Option.get! (State.felts st { name := "%31" }) *
            (Option.get! (State.felts st { name := "%0" }) -
              Option.get!
                (State.felts st
                  {
                    name :=
                      "%31" }))) 

-- Run the whole program by using part24_state rather than Code.part24
def part24_state_update (st: State): State :=
  Γ (part24_state st) ⟦Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part24_state for Code.part24 produces the same result
lemma part24_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part24_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part24
  MLIR
  unfold part24_state_update part24_state
  rewrite [←eq]
  rfl

lemma part24_updates_opaque {st : State} : 
  Code.getReturn (part23_state_update st) ↔
  Code.getReturn (part24_state_update (part23_state st)) := by
  simp [part23_state_update, part24_wp]

end Risc0.OneHot20.Constraints.WP