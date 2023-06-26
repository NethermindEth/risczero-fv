import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart14

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part15 on st
def part15_state (st: State) : State :=
  
          (State.set!
            ((State.set! st { name := "data" } 15 (Option.get! st.felts[({ name := "%97" }: FeltVar)]!)[felts][{ name := "%98" }] ←
                ↑(Bitvec.toNat
                    (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%21" }))))
                      (Bitvec.ofNat 256
                        (ZMod.val (Option.get! (State.felts st { name := "%1" })))))))[felts][{ name := "%99" }] ←
              ↑(Bitvec.toNat
                    (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%21" }))))
                      (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%1" })))))) *
                Option.get! (State.felts st { name := "%14" }))
            { name := "data" } 5
            (↑(Bitvec.toNat
                  (Bitvec.and (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%21" }))))
                    (Bitvec.ofNat 256 (ZMod.val (Option.get! (State.felts st { name := "%1" })))))) *
              Option.get!
                (State.felts st
                  {
                    name :=
                      "%14" }))) 

-- Run the program from part15 onwards by using part15_state rather than Code.part15
def part15_state_update (st: State): State :=
  Γ (part15_state st) ⟦Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31⟧

-- Prove that substituting part15_state for Code.part15 produces the same result
lemma part15_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part15_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) = prog
  unfold Code.part15
  MLIR
  rewrite [←eq]
  unfold part15_state_update part15_state
  rfl

lemma part15_updates_opaque {st : State} : 
  Code.getReturn (part14_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part15_state_update (part14_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part14_state_update, part15_wp]

end Risc0.ComputeDecode.Witness.WP