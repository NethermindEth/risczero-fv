import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart5

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part6 on st
def part6_state (st: State) : State :=
  State.set!
            ((st[felts][{ name := "%74" }] ←
                feltBitAnd (Option.get! (State.felts st { name := "%23" }))
                  (Option.get! (State.felts st { name := "%19" })))[felts][{ name := "%75" }] ←
              feltBitAnd (Option.get! (State.felts st { name := "%23" }))
                  (Option.get! (State.felts st { name := "%19" })) *
                Option.get! (State.felts st { name := "%18" }))
            { name := "data" } 10
            (feltBitAnd (Option.get! (State.felts st { name := "%23" }))
                (Option.get! (State.felts st { name := "%19" })) *
              Option.get! (State.felts st { name := "%18" }))[felts][{ name := "%76" }] ←
          feltBitAnd (Option.get! (State.felts st { name := "%23" }))
            (Option.get! (State.felts st { name := "%17" }))

-- Run the program from part6 onwards by using part6_state rather than Code.part6
def part6_state_update (st: State): State :=
  Γ (part6_state st) ⟦Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31⟧

-- Prove that substituting part6_state for Code.part6 produces the same result
lemma part6_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part6_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) = prog
  unfold Code.part6
  MLIR
  rewrite [←eq]
  unfold part6_state_update part6_state
  rfl

lemma part6_updates_opaque {st : State} : 
  Code.getReturn (part5_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part6_state_update (part5_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part5_state_update, part6_wp]

end Risc0.ComputeDecode.Witness.WP