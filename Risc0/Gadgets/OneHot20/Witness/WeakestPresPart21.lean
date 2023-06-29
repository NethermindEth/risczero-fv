import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart20

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part21 on st
def part21_state (st: State) : State :=
  
          ((((st["%25"] ←ₛ getImpl st { name := "data" } 0 3)[felts][{ name := "%26" }] ←
                Option.get! (State.felts (st["%25"] ←ₛ getImpl st { name := "data" } 0 3) { name := "%25" }) *
                  Option.get! (State.felts st { name := "%16" }))[felts][{ name := "%27" }] ←
              Option.get! (State.felts st { name := "%24" }) +
                Option.get! (State.felts (st["%25"] ←ₛ getImpl st { name := "data" } 0 3) { name := "%25" }) *
                  Option.get! (State.felts st { name := "%16" }))["%28"] ←ₛ
            getImpl st { name := "data" } 0
              4) 

-- Run the program from part21 onwards by using part21_state rather than Code.part21
def part21_state_update (st: State): State :=
  Γ (part21_state st) ⟦Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part21_state for Code.part21 produces the same result
lemma part21_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part21_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part21
  MLIR
  rewrite [←eq]
  unfold part21_state_update part21_state
  rfl

lemma part21_updates_opaque {st : State} : 
  Code.getReturn (part20_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part21_state_update (part20_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part20_state_update, part21_wp]

end Risc0.OneHot20.Witness.WP