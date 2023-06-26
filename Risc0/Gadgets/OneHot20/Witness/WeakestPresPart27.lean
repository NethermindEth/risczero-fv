import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart26

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part27 on st
def part27_state (st: State) : State :=
  
          ((((st["%49"] ←ₛ getImpl st { name := "data" } 0 11)[felts][{ name := "%50" }] ←
                Option.get! (State.felts (st["%49"] ←ₛ getImpl st { name := "data" } 0 11) { name := "%49" }) *
                  Option.get!
                    (State.felts (st["%49"] ←ₛ getImpl st { name := "data" } 0 11)
                      { name := "%8" }))[felts][{ name := "%51" }] ←
              Option.get!
                  (((st["%49"] ←ₛ getImpl st { name := "data" } 0 11).felts[{ name := "%50" }] ←ₘ
                      Option.get! (State.felts (st["%49"] ←ₛ getImpl st { name := "data" } 0 11) { name := "%49" }) *
                        Option.get! (State.felts (st["%49"] ←ₛ getImpl st { name := "data" } 0 11) { name := "%8" }))
                    { name := "%48" }) +
                Option.get! (State.felts (st["%49"] ←ₛ getImpl st { name := "data" } 0 11) { name := "%49" }) *
                  Option.get!
                    (State.felts (st["%49"] ←ₛ getImpl st { name := "data" } 0 11) { name := "%8" }))["%52"] ←ₛ
            getImpl (st["%49"] ←ₛ getImpl st { name := "data" } 0 11) { name := "data" } 0
              12) 

-- Run the program from part27 onwards by using part27_state rather than Code.part27
def part27_state_update (st: State): State :=
  Γ (part27_state st) ⟦Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part27_state for Code.part27 produces the same result
lemma part27_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part27_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part27
  MLIR
  rewrite [←eq]
  unfold part27_state_update part27_state
  rfl

lemma part27_updates_opaque {st : State} : 
  Code.getReturn (part26_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part27_state_update (part26_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part26_state_update, part27_wp]

end Risc0.OneHot20.Witness.WP