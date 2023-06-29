import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart10

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part11 on st
def part11_state (st: State) : State :=
  
          (State.set!
              ((st[felts][{ name := "%87" }] ←
                  ↑(Bitvec.toNat
                      (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%22" }))))
                        (Bitvec.ofNat 256
                          (ZMod.val (Option.get! (State.felts st { name := "%17" })))))))[felts][{ name := "%88" }] ←
                ↑(Bitvec.toNat
                      (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%22" }))))
                        (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%17" })))))) *
                  Option.get! (State.felts st { name := "%16" }))
              { name := "data" } 2
              (↑(Bitvec.toNat
                    (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%22" }))))
                      (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%17" })))))) *
                Option.get! (State.felts st { name := "%16" }))[felts][{ name := "%89" }] ←
            ↑(Bitvec.toNat
                (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%22" }))))
                  (Bitvec.ofNat 256
                    (ZMod.val
                      (Option.get!
                        (State.felts st
                          {
                            name :=
                              "%15" }))))))) 

-- Run the program from part11 onwards by using part11_state rather than Code.part11
def part11_state_update (st: State): State :=
  Γ (part11_state st) ⟦Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31⟧

-- Prove that substituting part11_state for Code.part11 produces the same result
lemma part11_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part11_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) = prog
  unfold Code.part11
  MLIR
  rewrite [←eq]
  unfold part11_state_update part11_state
  rfl

lemma part11_updates_opaque {st : State} : 
  Code.getReturn (part10_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part11_state_update (part10_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part10_state_update, part11_wp]

end Risc0.ComputeDecode.Witness.WP