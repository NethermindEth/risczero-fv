import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart26

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part27 on st
def part27_state (st: State) : State := 
  
        ((((st[props][{ name := "%108" }] ←
                (Option.get! (State.props st { name := "%104" }) ∧
                  Option.get! (State.felts st { name := "%107" }) = 0))[felts][{ name := "%109" }] ←
              Option.get! (State.felts st { name := "%105" }) +
                Option.get! (State.felts st { name := "%37" }))[felts][{ name := "%110" }] ←
            Option.get! (State.felts st { name := "%0" }) -
              Option.get! (State.felts st { name := "%40" }))[felts][{ name := "%111" }] ←
          Option.get! (State.felts st { name := "%40" }) *
            (Option.get! (State.felts st { name := "%0" }) -
              Option.get!
                (State.felts st
                  {
                    name :=
                      "%40" }))) 

-- Run the whole program by using part27_state rather than Code.part27
def part27_state_update (st: State): State :=
  Γ (part27_state st) ⟦Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part27_state for Code.part27 produces the same result
lemma part27_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part27_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part27
  MLIR
  unfold part27_state_update part27_state
  rewrite [←eq]
  rfl

lemma part27_updates_opaque {st : State} : 
  Code.getReturn (part26_state_update st) ↔
  Code.getReturn (part27_state_update (part26_state st)) := by
  simp [part26_state_update, part27_wp]

end Risc0.OneHot20.Constraints.WP