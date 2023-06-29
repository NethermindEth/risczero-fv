import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart11

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part12 on st
def part12_state (st: State) : State :=
  
          ((State.set!
                (st[felts][{ name := "%90" }] ←
                  Option.get! (State.felts st { name := "%89" }) * Option.get! (State.felts st { name := "%14" }))
                { name := "data" } 11
                (Option.get! (State.felts st { name := "%89" }) *
                  Option.get! (State.felts st { name := "%14" }))[felts][{ name := "%91" }] ←
              ↑(Bitvec.toNat
                  (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%22" }))))
                    (Bitvec.ofNat 256
                      (ZMod.val (Option.get! (State.felts st { name := "%6" })))))))[felts][{ name := "%92" }] ←
            ↑(Bitvec.toNat
                  (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%22" }))))
                    (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%6" })))))) *
              Option.get!
                (State.felts st
                  {
                    name :=
                      "%5" })) 

-- Run the program from part12 onwards by using part12_state rather than Code.part12
def part12_state_update (st: State): State :=
  Γ (part12_state st) ⟦Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31⟧

-- Prove that substituting part12_state for Code.part12 produces the same result
lemma part12_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part12_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) = prog
  unfold Code.part12
  MLIR
  rewrite [←eq]
  unfold part12_state_update part12_state
  rfl

lemma part12_updates_opaque {st : State} : 
  Code.getReturn (part11_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part12_state_update (part11_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part11_state_update, part12_wp]

end Risc0.ComputeDecode.Witness.WP