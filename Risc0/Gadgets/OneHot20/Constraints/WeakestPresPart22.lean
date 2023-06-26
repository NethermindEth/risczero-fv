import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart21

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part22 on st
def part22_state (st: State) : State := 
  
        ((((st[props][{ name := "%88" }] ←
                (Option.get! (State.props st { name := "%84" }) ∧
                  Option.get! (State.felts st { name := "%87" }) = 0))[felts][{ name := "%89" }] ←
              Option.get! (State.felts st { name := "%85" }) +
                Option.get! (State.felts st { name := "%22" }))[felts][{ name := "%90" }] ←
            Option.get! (State.felts st { name := "%0" }) -
              Option.get! (State.felts st { name := "%25" }))[felts][{ name := "%91" }] ←
          Option.get! (State.felts st { name := "%25" }) *
            (Option.get! (State.felts st { name := "%0" }) -
              Option.get!
                (State.felts st
                  {
                    name :=
                      "%25" }))) 

-- Run the whole program by using part22_state rather than Code.part22
def part22_state_update (st: State): State :=
  Γ (part22_state st) ⟦Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part22_state for Code.part22 produces the same result
lemma part22_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part22_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part22
  MLIR
  unfold part22_state_update part22_state
  rewrite [←eq]
  rfl

lemma part22_updates_opaque {st : State} : 
  Code.getReturn (part21_state_update st) ↔
  Code.getReturn (part22_state_update (part21_state st)) := by
  simp [part21_state_update, part22_wp]

end Risc0.OneHot20.Constraints.WP