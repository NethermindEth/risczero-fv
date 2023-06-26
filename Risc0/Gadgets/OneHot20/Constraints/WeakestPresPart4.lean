import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart3

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part4 on st
def part4_state (st: State) : State := 
  
        ((((st[felts][{ name := "%16" }] ← 17)[felts][{ name := "%17" }] ← 18)[felts][{ name := "%18" }] ←
            19)[props][{ name := "%19" }] ←
          True) 

-- Run the whole program by using part4_state rather than Code.part4
def part4_state_update (st: State): State :=
  Γ (part4_state st) ⟦Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part4_state for Code.part4 produces the same result
lemma part4_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part4; Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part4_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part4
  MLIR
  unfold part4_state_update part4_state
  rewrite [←eq]
  rfl

lemma part4_updates_opaque {st : State} : 
  Code.getReturn (part3_state_update st) ↔
  Code.getReturn (part4_state_update (part3_state st)) := by
  simp [part3_state_update, part4_wp]

end Risc0.OneHot20.Constraints.WP