import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart15

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part16 on st
def part16_state (st: State) : State :=
  
          (State.set!
              ((st[felts][{ name := "%100" }] ←
                  ↑(Bitvec.toNat
                      (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%21" }))))
                        (Bitvec.ofNat 256
                          (ZMod.val (Option.get! (State.felts st { name := "%6" })))))))[felts][{ name := "%101" }] ←
                ↑(Bitvec.toNat
                      (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%21" }))))
                        (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%6" })))))) *
                  Option.get! (State.felts st { name := "%5" }))
              { name := "data" } 7
              (↑(Bitvec.toNat
                    (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%21" }))))
                      (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%6" })))))) *
                Option.get! (State.felts st { name := "%5" }))[felts][{ name := "%102" }] ←
            ↑(Bitvec.toNat
                (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%21" }))))
                  (Bitvec.ofNat 256
                    (ZMod.val
                      (Option.get!
                        (State.felts st
                          {
                            name :=
                              "%4" }))))))) 

-- Run the program from part16 onwards by using part16_state rather than Code.part16
def part16_state_update (st: State): State :=
  Γ (part16_state st) ⟦Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31⟧

-- Prove that substituting part16_state for Code.part16 produces the same result
lemma part16_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part16_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) = prog
  unfold Code.part16
  MLIR
  rewrite [←eq]
  unfold part16_state_update part16_state
  rfl

lemma part16_updates_opaque {st : State} : 
  Code.getReturn (part15_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part16_state_update (part15_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part15_state_update, part16_wp]

end Risc0.ComputeDecode.Witness.WP