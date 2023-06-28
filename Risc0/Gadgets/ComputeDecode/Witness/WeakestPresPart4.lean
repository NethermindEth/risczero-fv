import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart3

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part4 on st
def part4_state (st: State) : State :=
  
          ((((st[felts][{ name := "%16" }] ← 1950351361)[felts][{ name := "%17" }] ← 96)[felts][{ name := "%18" }] ←
              1997537281)[felts][{ name := "%19" }] ←
            128) 

-- Run the program from part4 onwards by using part4_state rather than Code.part4
def part4_state_update (st: State): State :=
  Γ (part4_state st) ⟦Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31⟧

-- Prove that substituting part4_state for Code.part4 produces the same result
lemma part4_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part4; Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part4_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) = prog
  unfold Code.part4
  MLIR
  rewrite [←eq]
  unfold part4_state_update part4_state
  rfl

lemma part4_updates_opaque {st : State} : 
  Code.getReturn (part3_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part4_state_update (part3_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part3_state_update, part4_wp]

end Risc0.ComputeDecode.Witness.WP