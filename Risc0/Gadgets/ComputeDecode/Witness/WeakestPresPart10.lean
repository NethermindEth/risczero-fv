import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart9

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part10 on st
def part10_state (st: State) : State :=
  
          (State.set!
            (((st[felts][{ name := "%91" }] ←
                  feltBitAnd (Option.get! (State.felts st { name := "%22" }))
                    (Option.get! (State.felts st { name := "%6" })))[felts][{ name := "%5" }] ←
                1509949441)[felts][{ name := "%92" }] ←
              feltBitAnd (Option.get! (State.felts st { name := "%22" }))
                  (Option.get! (State.felts st { name := "%6" })) *
                1509949441)
            { name := "data" } 4
            (feltBitAnd (Option.get! (State.felts st { name := "%22" }))
                (Option.get! (State.felts st { name := "%6" })) *
              1509949441)) 

def part10_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (st) ⟨"%91"⟩) ⟨"%92"⟩

-- Run the program from part10 onwards by using part10_state rather than Code.part10
def part10_state_update (st: State): State :=
  Γ (part10_drops (part10_state st)) ⟦Code.part11;dropfelt ⟨"%93"⟩;Code.part12;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;Code.part13;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;Code.part14;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part15;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;Code.part16;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;Code.part17;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;Code.part18;dropfelt ⟨"%26"⟩;Code.part19;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;Code.part20;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;Code.part21;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;Code.part22;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;Code.part23;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part24;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;Code.part25;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;Code.part26;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;Code.part27;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;Code.part28;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩⟧

-- Prove that substituting part10_state for Code.part10 produces the same result
lemma part10_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part10;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;Code.part11;dropfelt ⟨"%93"⟩;Code.part12;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;Code.part13;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;Code.part14;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part15;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;Code.part16;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;Code.part17;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;Code.part18;dropfelt ⟨"%26"⟩;Code.part19;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;Code.part20;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;Code.part21;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;Code.part22;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;Code.part23;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part24;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;Code.part25;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;Code.part26;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;Code.part27;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;Code.part28;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part10_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;Code.part11;dropfelt ⟨"%93"⟩;Code.part12;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;Code.part13;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;Code.part14;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;Code.part15;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;Code.part16;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;Code.part17;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;Code.part18;dropfelt ⟨"%26"⟩;Code.part19;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;Code.part20;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;Code.part21;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;Code.part22;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;Code.part23;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part24;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;Code.part25;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;Code.part26;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;Code.part27;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;Code.part28;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) = prog
  unfold Code.part10
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part10_state_update part10_drops part10_state
  rfl

lemma part10_updates_opaque {st : State} : 
  Code.getReturn (part9_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part10_state_update (part9_drops (part9_state st))) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part9_state_update, part10_wp]

end Risc0.ComputeDecode.Witness.WP