import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart14

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part15 on st
def part15_state (st: State) : State := 
  
        ((((st[felts][{ name := "%60" }] ←
                Option.get! (State.felts st { name := "%57" }) +
                  Option.get! (State.felts st { name := "%59" }))["%61"] ←ₛ
              getImpl st { name := "data" } 0 15)[felts][{ name := "%62" }] ←
            Option.get!
                (State.felts
                  ((st[felts][{ name := "%60" }] ←
                      Option.get! (State.felts st { name := "%57" }) +
                        Option.get! (State.felts st { name := "%59" }))["%61"] ←ₛ
                    getImpl st { name := "data" } 0 15)
                  { name := "%61" }) *
              Option.get!
                (State.felts
                  ((st[felts][{ name := "%60" }] ←
                      Option.get! (State.felts st { name := "%57" }) +
                        Option.get! (State.felts st { name := "%59" }))["%61"] ←ₛ
                    getImpl st { name := "data" } 0 15)
                  { name := "%14" }))[felts][{ name := "%63" }] ←
          Option.get!
              ((((st[felts][{ name := "%60" }] ←
                        Option.get! (State.felts st { name := "%57" }) +
                          Option.get! (State.felts st { name := "%59" }))["%61"] ←ₛ
                      getImpl st { name := "data" } 0 15).felts[{ name := "%62" }] ←ₘ
                  Option.get!
                      (State.felts
                        ((st[felts][{ name := "%60" }] ←
                            Option.get! (State.felts st { name := "%57" }) +
                              Option.get! (State.felts st { name := "%59" }))["%61"] ←ₛ
                          getImpl st { name := "data" } 0 15)
                        { name := "%61" }) *
                    Option.get!
                      (State.felts
                        ((st[felts][{ name := "%60" }] ←
                            Option.get! (State.felts st { name := "%57" }) +
                              Option.get! (State.felts st { name := "%59" }))["%61"] ←ₛ
                          getImpl st { name := "data" } 0 15)
                        { name := "%14" }))
                { name := "%60" }) +
            Option.get!
                (State.felts
                  ((st[felts][{ name := "%60" }] ←
                      Option.get! (State.felts st { name := "%57" }) +
                        Option.get! (State.felts st { name := "%59" }))["%61"] ←ₛ
                    getImpl st { name := "data" } 0 15)
                  { name := "%61" }) *
              Option.get!
                (State.felts
                  ((st[felts][{ name := "%60" }] ←
                      Option.get! (State.felts st { name := "%57" }) +
                        Option.get! (State.felts st { name := "%59" }))["%61"] ←ₛ
                    getImpl st { name := "data" } 0 15)
                  {
                    name :=
                      "%14" })) 

-- Run the whole program by using part15_state rather than Code.part15
def part15_state_update (st: State): State :=
  Γ (part15_state st) ⟦Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part15_state for Code.part15 produces the same result
lemma part15_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part15_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part15
  MLIR
  unfold part15_state_update part15_state
  rewrite [←eq]
  rfl

lemma part15_updates_opaque {st : State} : 
  Code.getReturn (part14_state_update st) ↔
  Code.getReturn (part15_state_update (part14_state st)) := by
  simp [part14_state_update, part15_wp]

end Risc0.OneHot20.Constraints.WP