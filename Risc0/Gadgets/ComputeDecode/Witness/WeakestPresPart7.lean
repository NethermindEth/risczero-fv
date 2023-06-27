import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart6

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part7 on st
def part7_state (st: State) : State :=
  (State.set!
              (st[felts][{ name := "%77" }] ←
                Option.get! (State.felts st { name := "%76" }) * Option.get! (State.felts st { name := "%16" }))
              { name := "data" } 1
              (Option.get! (State.felts st { name := "%76" }) *
                Option.get! (State.felts st { name := "%16" }))[felts][{ name := "%78" }] ←
            feltBitAnd (Option.get! (State.felts st { name := "%23" }))
              (Option.get! (State.felts st { name := "%15" })))[felts][{ name := "%79" }] ←
          feltBitAnd (Option.get! (State.felts st { name := "%23" })) (Option.get! (State.felts st { name := "%15" })) *
            Option.get! (State.felts st { name := "%14" })

-- Run the program from part7 onwards by using part7_state rather than Code.part7
def part7_state_update (st: State): State :=
  Γ (part7_state st) ⟦Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31⟧

-- Prove that substituting part7_state for Code.part7 produces the same result
lemma part7_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part7_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) = prog
  unfold Code.part7
  MLIR
  rewrite [←eq]
  unfold part7_state_update part7_state
  rfl

lemma part7_updates_opaque {st : State} : 
  Code.getReturn (part6_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part7_state_update (part6_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part6_state_update, part7_wp]

end Risc0.ComputeDecode.Witness.WP