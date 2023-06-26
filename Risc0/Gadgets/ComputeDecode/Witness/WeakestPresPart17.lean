import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart16

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part17 on st
def part17_state (st: State) : State :=
  
          (State.set!
            ((State.set! st { name := "data" } 6
                  (Option.get! st.felts[({ name := "%102" }: FeltVar)]!)[felts][{ name := "%103" }] ←
                ↑(Bitvec.toNat
                    (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%20" }))))
                      (Bitvec.ofNat 256
                        (ZMod.val (Option.get! (State.felts st { name := "%19" })))))))[felts][{ name := "%104" }] ←
              ↑(Bitvec.toNat
                    (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%20" }))))
                      (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%19" })))))) *
                Option.get! (State.felts st { name := "%18" }))
            { name := "data" } 16
            (↑(Bitvec.toNat
                  (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%20" }))))
                    (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%19" })))))) *
              Option.get!
                (State.felts st
                  {
                    name :=
                      "%18" }))) 

-- Run the program from part17 onwards by using part17_state rather than Code.part17
def part17_state_update (st: State): State :=
  Γ (part17_state st) ⟦Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31⟧

-- Prove that substituting part17_state for Code.part17 produces the same result
lemma part17_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part17_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) = prog
  unfold Code.part17
  MLIR
  rewrite [←eq]
  unfold part17_state_update part17_state
  rfl

lemma part17_updates_opaque {st : State} : 
  Code.getReturn (part16_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part17_state_update (part16_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part16_state_update, part17_wp]

end Risc0.ComputeDecode.Witness.WP