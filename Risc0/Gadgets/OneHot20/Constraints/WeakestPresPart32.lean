import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart31

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part32 on st
def part32_state (st: State) : State := 
  
        ((((st[props][{ name := "%128" }] ←
                (Option.get! (State.props st { name := "%124" }) ∧
                  Option.get! (State.felts st { name := "%127" }) = 0))[felts][{ name := "%129" }] ←
              Option.get! (State.felts st { name := "%125" }) +
                Option.get! (State.felts st { name := "%52" }))[felts][{ name := "%130" }] ←
            Option.get! (State.felts st { name := "%0" }) -
              Option.get! (State.felts st { name := "%55" }))[felts][{ name := "%131" }] ←
          Option.get! (State.felts st { name := "%55" }) *
            (Option.get! (State.felts st { name := "%0" }) -
              Option.get!
                (State.felts st
                  {
                    name :=
                      "%55" }))) 

-- Run the whole program by using part32_state rather than Code.part32
def part32_state_update (st: State): State :=
  Γ (part32_state st) ⟦Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part32_state for Code.part32 produces the same result
lemma part32_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part32_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part32
  MLIR
  unfold part32_state_update part32_state
  rewrite [←eq]
  rfl

lemma part32_updates_opaque {st : State} : 
  Code.getReturn (part31_state_update st) ↔
  Code.getReturn (part32_state_update (part31_state st)) := by
  simp [part31_state_update, part32_wp]

end Risc0.OneHot20.Constraints.WP