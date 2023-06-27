import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart33

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part34 on st
def part34_state (st: State) : State :=
  
          ((((withEqZero (Option.get! st.felts[({ name := "%76" }: FeltVar)]!) st)["%77"] ←ₛ
                getImpl st { name := "data" } 0 0)[felts][{ name := "%78" }] ←
              Option.get!
                  (State.felts
                    ((withEqZero (Option.get! st.felts[({ name := "%76" }: FeltVar)]!) st)["%77"] ←ₛ
                      getImpl st { name := "data" } 0 0)
                    { name := "%18" }) -
                Option.get!
                  (State.felts
                    ((withEqZero (Option.get! st.felts[({ name := "%76" }: FeltVar)]!) st)["%77"] ←ₛ
                      getImpl st { name := "data" } 0 0)
                    { name := "%77" }))[felts][{ name := "%79" }] ←
            Option.get!
                ((((withEqZero (Option.get! st.felts[({ name := "%76" }: FeltVar)]!) st)["%77"] ←ₛ
                        getImpl st { name := "data" } 0 0).felts[{ name := "%78" }] ←ₘ
                    Option.get!
                        (State.felts
                          ((withEqZero (Option.get! st.felts[({ name := "%76" }: FeltVar)]!) st)["%77"] ←ₛ
                            getImpl st { name := "data" } 0 0)
                          { name := "%18" }) -
                      Option.get!
                        (State.felts
                          ((withEqZero (Option.get! st.felts[({ name := "%76" }: FeltVar)]!) st)["%77"] ←ₛ
                            getImpl st { name := "data" } 0 0)
                          { name := "%77" }))
                  { name := "%77" }) *
              (Option.get!
                  (State.felts
                    ((withEqZero (Option.get! st.felts[({ name := "%76" }: FeltVar)]!) st)["%77"] ←ₛ
                      getImpl st { name := "data" } 0 0)
                    { name := "%18" }) -
                Option.get!
                  (State.felts
                    ((withEqZero (Option.get! st.felts[({ name := "%76" }: FeltVar)]!) st)["%77"] ←ₛ
                      getImpl st { name := "data" } 0 0)
                    {
                      name :=
                        "%77" }))) 

-- Run the program from part34 onwards by using part34_state rather than Code.part34
def part34_state_update (st: State): State :=
  Γ (part34_state st) ⟦Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part34_state for Code.part34 produces the same result
lemma part34_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part34_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part34
  MLIR
  rewrite [←eq]
  unfold part34_state_update part34_state
  rfl

lemma part34_updates_opaque {st : State} : 
  Code.getReturn (part33_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part34_state_update (part33_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part33_state_update, part34_wp]

end Risc0.OneHot20.Witness.WP