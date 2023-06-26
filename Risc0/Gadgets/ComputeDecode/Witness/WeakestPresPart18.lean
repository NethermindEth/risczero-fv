import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart17

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part18 on st
def part18_state (st: State) : State :=
  
          ((State.set!
                (st[felts][{ name := "%105" }] ←
                  ↑(Bitvec.toNat
                      (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%20" }))))
                        (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%0" })))))))
                { name := "data" } 17
                ↑(Bitvec.toNat
                    (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%20" }))))
                      (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%0" }))))))["%24"] ←ₛ
              getImpl
                (State.set!
                  (st[felts][{ name := "%105" }] ←
                    ↑(Bitvec.toNat
                        (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%20" }))))
                          (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%0" })))))))
                  { name := "data" } 17
                  ↑(Bitvec.toNat
                      (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%20" }))))
                        (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%0" })))))))
                { name := "data" } 0 13)["%25"] ←ₛ
            getImpl
              (State.set!
                (st[felts][{ name := "%105" }] ←
                  ↑(Bitvec.toNat
                      (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%20" }))))
                        (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%0" })))))))
                { name := "data" } 17
                ↑(Bitvec.toNat
                    (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%20" }))))
                      (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%0" })))))))
              { name := "data" } 0
              0) 

-- Run the program from part18 onwards by using part18_state rather than Code.part18
def part18_state_update (st: State): State :=
  Γ (part18_state st) ⟦Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31⟧

-- Prove that substituting part18_state for Code.part18 produces the same result
lemma part18_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part18_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) = prog
  unfold Code.part18
  MLIR
  rewrite [←eq]
  unfold part18_state_update part18_state
  rfl

lemma part18_updates_opaque {st : State} : 
  Code.getReturn (part17_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part18_state_update (part17_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part17_state_update, part18_wp]

end Risc0.ComputeDecode.Witness.WP