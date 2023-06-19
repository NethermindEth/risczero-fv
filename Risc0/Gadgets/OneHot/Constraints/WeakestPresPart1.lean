import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Constraints.Code
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart0

namespace Risc0.OneHot.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part₁ on st
def part₁_state (st: State) : State := (st["output[1]"] ←ₛ
          if
              0 ≤ st.cycle ∧
                { name := "output" } ∈ st.vars ∧
                  1 < Map.get! st.bufferWidths { name := "output" } ∧
                    Option.isSome
                        (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 1)) =
                      true then
            some
              (Lit.Val
                (Option.get! (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 1))))
          else none)["output[2]"] ←ₛ
        if
            0 ≤
                (st["output[1]"] ←ₛ
                    if
                        0 ≤ st.cycle ∧
                          { name := "output" } ∈ st.vars ∧
                            1 < Map.get! st.bufferWidths { name := "output" } ∧
                              Option.isSome
                                  (Buffer.get! (Map.get! st.buffers { name := "output" })
                                    (st.cycle - Back.toNat 0, 1)) =
                                true then
                      some
                        (Lit.Val
                          (Option.get!
                            (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 1))))
                    else none).cycle ∧
              { name := "output" } ∈
                  (st["output[1]"] ←ₛ
                      if
                          0 ≤ st.cycle ∧
                            { name := "output" } ∈ st.vars ∧
                              1 < Map.get! st.bufferWidths { name := "output" } ∧
                                Option.isSome
                                    (Buffer.get! (Map.get! st.buffers { name := "output" })
                                      (st.cycle - Back.toNat 0, 1)) =
                                  true then
                        some
                          (Lit.Val
                            (Option.get!
                              (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 1))))
                      else none).vars ∧
                2 <
                    Map.get!
                      (st["output[1]"] ←ₛ
                          if
                              0 ≤ st.cycle ∧
                                { name := "output" } ∈ st.vars ∧
                                  1 < Map.get! st.bufferWidths { name := "output" } ∧
                                    Option.isSome
                                        (Buffer.get! (Map.get! st.buffers { name := "output" })
                                          (st.cycle - Back.toNat 0, 1)) =
                                      true then
                            some
                              (Lit.Val
                                (Option.get!
                                  (Buffer.get! (Map.get! st.buffers { name := "output" })
                                    (st.cycle - Back.toNat 0, 1))))
                          else none).bufferWidths
                      { name := "output" } ∧
                  Option.isSome
                      (Buffer.get!
                        (Map.get!
                          (st["output[1]"] ←ₛ
                              if
                                  0 ≤ st.cycle ∧
                                    { name := "output" } ∈ st.vars ∧
                                      1 < Map.get! st.bufferWidths { name := "output" } ∧
                                        Option.isSome
                                            (Buffer.get! (Map.get! st.buffers { name := "output" })
                                              (st.cycle - Back.toNat 0, 1)) =
                                          true then
                                some
                                  (Lit.Val
                                    (Option.get!
                                      (Buffer.get! (Map.get! st.buffers { name := "output" })
                                        (st.cycle - Back.toNat 0, 1))))
                              else none).buffers
                          { name := "output" })
                        ((st["output[1]"] ←ₛ
                                if
                                    0 ≤ st.cycle ∧
                                      { name := "output" } ∈ st.vars ∧
                                        1 < Map.get! st.bufferWidths { name := "output" } ∧
                                          Option.isSome
                                              (Buffer.get! (Map.get! st.buffers { name := "output" })
                                                (st.cycle - Back.toNat 0, 1)) =
                                            true then
                                  some
                                    (Lit.Val
                                      (Option.get!
                                        (Buffer.get! (Map.get! st.buffers { name := "output" })
                                          (st.cycle - Back.toNat 0, 1))))
                                else none).cycle -
                            Back.toNat 0,
                          2)) =
                    true then
          some
            (Lit.Val
              (Option.get!
                (Buffer.get!
                  (Map.get!
                    (st["output[1]"] ←ₛ
                        if
                            0 ≤ st.cycle ∧
                              { name := "output" } ∈ st.vars ∧
                                1 < Map.get! st.bufferWidths { name := "output" } ∧
                                  Option.isSome
                                      (Buffer.get! (Map.get! st.buffers { name := "output" })
                                        (st.cycle - Back.toNat 0, 1)) =
                                    true then
                          some
                            (Lit.Val
                              (Option.get!
                                (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 1))))
                        else none).buffers
                    { name := "output" })
                  ((st["output[1]"] ←ₛ
                          if
                              0 ≤ st.cycle ∧
                                { name := "output" } ∈ st.vars ∧
                                  1 < Map.get! st.bufferWidths { name := "output" } ∧
                                    Option.isSome
                                        (Buffer.get! (Map.get! st.buffers { name := "output" })
                                          (st.cycle - Back.toNat 0, 1)) =
                                      true then
                            some
                              (Lit.Val
                                (Option.get!
                                  (Buffer.get! (Map.get! st.buffers { name := "output" })
                                    (st.cycle - Back.toNat 0, 1))))
                          else none).cycle -
                      Back.toNat 0,
                    2))))
        else none

-- Run the whole program by using part₁_state rather than Code.part₁
def part₁_state_update (st: State): State :=
  Γ (part₁_state st) ⟦Code.part₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆⟧

-- Prove that substituting part₁_state for Code.part₁ produces the same result
-- ****************************** WEAKEST PRE - Part₁ ******************************
lemma part₁_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part₁; Code.part₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆) st) ↔
  Code.getReturn (part₁_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆) = prog
  unfold Code.part₁
  MLIR
  unfold part₁_state_update part₁_state
  rewrite [←eq]
  rfl
-- ****************************** WEAKEST PRE - Part₁ ******************************

lemma part₁_updates_opaque {st : State} : 
  Code.getReturn (part₀_state_update st) ↔
  Code.getReturn (part₁_state_update (part₀_state st)) := by
  simp [part₀_state_update, part₁_wp]

end Risc0.OneHot.Constraints.WP
