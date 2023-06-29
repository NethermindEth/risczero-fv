import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart25

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part26 on st
def part26_state (st: State) : State := 
  
        ((((st[props][{ name := "%104" }] ←
                (Option.get! (State.props st { name := "%100" }) ∧
                  Option.get! (State.felts st { name := "%103" }) = 0))[felts][{ name := "%105" }] ←
              Option.get! (State.felts st { name := "%101" }) +
                Option.get! (State.felts st { name := "%34" }))[felts][{ name := "%106" }] ←
            Option.get! (State.felts st { name := "%0" }) -
              Option.get! (State.felts st { name := "%37" }))[felts][{ name := "%107" }] ←
          Option.get! (State.felts st { name := "%37" }) *
            (Option.get! (State.felts st { name := "%0" }) -
              Option.get!
                (State.felts st
                  {
                    name :=
                      "%37" }))) 

-- Run the whole program by using part26_state rather than Code.part26
def part26_state_update (st: State): State :=
  Γ (part26_state st) ⟦Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part26_state for Code.part26 produces the same result
lemma part26_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part26_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part26
  MLIR
  unfold part26_state_update part26_state
  rewrite [←eq]
  rfl

lemma part26_updates_opaque {st : State} : 
  Code.getReturn (part25_state_update st) ↔
  Code.getReturn (part26_state_update (part25_state st)) := by
  simp [part25_state_update, part26_wp]

end Risc0.OneHot20.Constraints.WP