import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart19

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part20 on st
def part20_state (st: State) : State :=
  
          ((((st["%21"] ←ₛ getImpl st { name := "data" } 0 1)["%22"] ←ₛ
                getImpl st { name := "data" } 0 2)[felts][{ name := "%23" }] ←
              Option.get! (State.felts (st["%22"] ←ₛ getImpl st { name := "data" } 0 2) { name := "%22" }) *
                Option.get! (State.felts st { name := "%17" }))[felts][{ name := "%24" }] ←
            Option.get! (State.felts (st["%21"] ←ₛ getImpl st { name := "data" } 0 1) { name := "%21" }) +
              Option.get! (State.felts (st["%22"] ←ₛ getImpl st { name := "data" } 0 2) { name := "%22" }) *
                Option.get!
                  (State.felts st
                    {
                      name :=
                        "%17" })) 

-- Run the program from part20 onwards by using part20_state rather than Code.part20
def part20_state_update (st: State): State :=
  Γ (part20_state st) ⟦Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part20_state for Code.part20 produces the same result
lemma part20_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part20_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part20
  MLIR
  rewrite [←eq]
  unfold part20_state_update part20_state
  rfl

lemma part20_updates_opaque {st : State} : 
  Code.getReturn (part19_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part20_state_update (part19_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part19_state_update, part20_wp]

end Risc0.OneHot20.Witness.WP