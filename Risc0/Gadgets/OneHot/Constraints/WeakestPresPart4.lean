import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Constraints.Code
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart3

namespace Risc0.OneHot.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part₄ on st
def part₄_state (st: State) : State :=
  ((((st[felts][{ name := "output[0]<=1" }] ←
              Option.get! (State.felts st { name := "output[0]" }) *
                Option.get! (State.felts st { name := "1-Output[0]" }))[props][{ name := "andEqz output[0]<=1" }] ←
            (Option.get! (State.props st { name := "andEqz 2*output[2]+output[1]-input" }) ∧
              (Option.get! (State.felts st { name := "output[0]" }) = 0 ∨
                Option.get! (State.felts st { name := "1-Output[0]" }) = 0)))[felts][{ name := "1-Output[1]" }] ←
          Option.get!
              ((st.felts[{ name := "output[0]<=1" }] ←ₘ
                  Option.get! (State.felts st { name := "output[0]" }) *
                    Option.get! (State.felts st { name := "1-Output[0]" }))
                { name := "1" }) -
            Option.get!
              ((st.felts[{ name := "output[0]<=1" }] ←ₘ
                  Option.get! (State.felts st { name := "output[0]" }) *
                    Option.get! (State.felts st { name := "1-Output[0]" }))
                { name := "output[1]" }))[felts][{ name := "output[1]<=1" }] ←
        Option.get!
            (((st.felts[{ name := "output[0]<=1" }] ←ₘ
                  Option.get! (State.felts st { name := "output[0]" }) *
                    Option.get! (State.felts st { name := "1-Output[0]" }))[{ name := "1-Output[1]" }] ←ₘ
                Option.get!
                    ((st.felts[{ name := "output[0]<=1" }] ←ₘ
                        Option.get! (State.felts st { name := "output[0]" }) *
                          Option.get! (State.felts st { name := "1-Output[0]" }))
                      { name := "1" }) -
                  Option.get!
                    ((st.felts[{ name := "output[0]<=1" }] ←ₘ
                        Option.get! (State.felts st { name := "output[0]" }) *
                          Option.get! (State.felts st { name := "1-Output[0]" }))
                      { name := "output[1]" }))
              { name := "output[1]" }) *
          (Option.get!
              ((st.felts[{ name := "output[0]<=1" }] ←ₘ
                  Option.get! (State.felts st { name := "output[0]" }) *
                    Option.get! (State.felts st { name := "1-Output[0]" }))
                { name := "1" }) -
            Option.get!
              ((st.felts[{ name := "output[0]<=1" }] ←ₘ
                  Option.get! (State.felts st { name := "output[0]" }) *
                    Option.get! (State.felts st { name := "1-Output[0]" }))
                { name := "output[1]" })))

-- Run the whole program by using part₄_state rather than Code.part₄
def part₄_state_update (st: State): State :=
  Γ (part₄_state st) ⟦Code.part₅; Code.part₆⟧

-- Prove that substituting part₄_state for Code.part₄ produces the same result
lemma part₄_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part₄; Code.part₅; Code.part₆) st) ↔
  Code.getReturn (part₄_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₅; Code.part₆) = prog
  unfold Code.part₄
  MLIR
  unfold part₄_state_update part₄_state
  rewrite [←eq]
  rfl

lemma part₄_updates_opaque {st : State} : 
  Code.getReturn (part₃_state_update st) ↔
  Code.getReturn (part₄_state_update (part₃_state st)) := by
  simp [part₃_state_update, part₄_wp]

end Risc0.OneHot.Constraints.WP
