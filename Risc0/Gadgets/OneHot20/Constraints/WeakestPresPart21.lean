import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart20

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part21 on st
def part21_state (st: State) : State := 
  
        ((((st[props][{ name := "%84" }] ←
                (Option.get! (State.props st { name := "%81" }) ∧
                  Option.get! (State.felts st { name := "%83" }) = 0))[felts][{ name := "%85" }] ←
              Option.get! (State.felts st { name := "%78" }) +
                Option.get! (State.felts st { name := "%21" }))[felts][{ name := "%86" }] ←
            Option.get! (State.felts st { name := "%0" }) -
              Option.get! (State.felts st { name := "%22" }))[felts][{ name := "%87" }] ←
          Option.get! (State.felts st { name := "%22" }) *
            (Option.get! (State.felts st { name := "%0" }) -
              Option.get!
                (State.felts st
                  {
                    name :=
                      "%22" }))) 

-- Run the whole program by using part21_state rather than Code.part21
def part21_state_update (st: State): State :=
  Γ (part21_state st) ⟦Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part21_state for Code.part21 produces the same result
lemma part21_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part21_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part21
  MLIR
  unfold part21_state_update part21_state
  rewrite [←eq]
  rfl

lemma part21_updates_opaque {st : State} : 
  Code.getReturn (part20_state_update st) ↔
  Code.getReturn (part21_state_update (part20_state st)) := by
  simp [part20_state_update, part21_wp]

end Risc0.OneHot20.Constraints.WP