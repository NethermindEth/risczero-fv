import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart27

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part28 on st
def part28_state (st: State) : State := 
  
        ((((st[props][{ name := "%112" }] ←
                (Option.get! (State.props st { name := "%108" }) ∧
                  Option.get! (State.felts st { name := "%111" }) = 0))[felts][{ name := "%113" }] ←
              Option.get! (State.felts st { name := "%109" }) +
                Option.get! (State.felts st { name := "%40" }))[felts][{ name := "%114" }] ←
            Option.get! (State.felts st { name := "%0" }) -
              Option.get! (State.felts st { name := "%43" }))[felts][{ name := "%115" }] ←
          Option.get! (State.felts st { name := "%43" }) *
            (Option.get! (State.felts st { name := "%0" }) -
              Option.get!
                (State.felts st
                  {
                    name :=
                      "%43" }))) 

-- Run the whole program by using part28_state rather than Code.part28
def part28_state_update (st: State): State :=
  Γ (part28_state st) ⟦Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part28_state for Code.part28 produces the same result
lemma part28_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part28_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part28
  MLIR
  unfold part28_state_update part28_state
  rewrite [←eq]
  rfl

lemma part28_updates_opaque {st : State} : 
  Code.getReturn (part27_state_update st) ↔
  Code.getReturn (part28_state_update (part27_state st)) := by
  simp [part27_state_update, part28_wp]

end Risc0.OneHot20.Constraints.WP