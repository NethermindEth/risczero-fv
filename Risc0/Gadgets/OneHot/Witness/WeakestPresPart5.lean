import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Witness.Code
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart4

namespace Risc0.OneHot.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part₅ on st
def part₅_state (st: State) : State := {
          buffers :=
            (st["output[0]"] ←ₛ
                if
                    0 ≤ st.cycle ∧
                      { name := "output" } ∈ st.vars ∧
                        0 < Map.get! st.bufferWidths { name := "output" } ∧
                          Option.isSome
                              (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 0)) =
                            true then
                  some
                    (Lit.Val
                      (Option.get!
                        (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 0))))
                else none).buffers,
          bufferWidths :=
            (st["output[0]"] ←ₛ
                if
                    0 ≤ st.cycle ∧
                      { name := "output" } ∈ st.vars ∧
                        0 < Map.get! st.bufferWidths { name := "output" } ∧
                          Option.isSome
                              (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 0)) =
                            true then
                  some
                    (Lit.Val
                      (Option.get!
                        (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 0))))
                else none).bufferWidths,
          constraints :=
            (Option.get!
                    (State.felts
                      (State.updateFelts
                        (st["output[0]"] ←ₛ
                          if
                              0 ≤ st.cycle ∧
                                { name := "output" } ∈ st.vars ∧
                                  0 < Map.get! st.bufferWidths { name := "output" } ∧
                                    Option.isSome
                                        (Buffer.get! (Map.get! st.buffers { name := "output" })
                                          (st.cycle - Back.toNat 0, 0)) =
                                      true then
                            some
                              (Lit.Val
                                (Option.get!
                                  (Buffer.get! (Map.get! st.buffers { name := "output" })
                                    (st.cycle - Back.toNat 0, 0))))
                          else none)
                        { name := "1 - Output[0]" }
                        (Option.get!
                            (State.felts
                              (st["output[0]"] ←ₛ
                                if
                                    0 ≤ st.cycle ∧
                                      { name := "output" } ∈ st.vars ∧
                                        0 < Map.get! st.bufferWidths { name := "output" } ∧
                                          Option.isSome
                                              (Buffer.get! (Map.get! st.buffers { name := "output" })
                                                (st.cycle - Back.toNat 0, 0)) =
                                            true then
                                  some
                                    (Lit.Val
                                      (Option.get!
                                        (Buffer.get! (Map.get! st.buffers { name := "output" })
                                          (st.cycle - Back.toNat 0, 0))))
                                else none)
                              { name := "1" }) -
                          Option.get!
                            (State.felts
                              (st["output[0]"] ←ₛ
                                if
                                    0 ≤ st.cycle ∧
                                      { name := "output" } ∈ st.vars ∧
                                        0 < Map.get! st.bufferWidths { name := "output" } ∧
                                          Option.isSome
                                              (Buffer.get! (Map.get! st.buffers { name := "output" })
                                                (st.cycle - Back.toNat 0, 0)) =
                                            true then
                                  some
                                    (Lit.Val
                                      (Option.get!
                                        (Buffer.get! (Map.get! st.buffers { name := "output" })
                                          (st.cycle - Back.toNat 0, 0))))
                                else none)
                              { name := "output[0]" })))
                      { name := "output[0]" }) =
                  0 ∨
                Option.get!
                    (State.felts
                      (State.updateFelts
                        (st["output[0]"] ←ₛ
                          if
                              0 ≤ st.cycle ∧
                                { name := "output" } ∈ st.vars ∧
                                  0 < Map.get! st.bufferWidths { name := "output" } ∧
                                    Option.isSome
                                        (Buffer.get! (Map.get! st.buffers { name := "output" })
                                          (st.cycle - Back.toNat 0, 0)) =
                                      true then
                            some
                              (Lit.Val
                                (Option.get!
                                  (Buffer.get! (Map.get! st.buffers { name := "output" })
                                    (st.cycle - Back.toNat 0, 0))))
                          else none)
                        { name := "1 - Output[0]" }
                        (Option.get!
                            (State.felts
                              (st["output[0]"] ←ₛ
                                if
                                    0 ≤ st.cycle ∧
                                      { name := "output" } ∈ st.vars ∧
                                        0 < Map.get! st.bufferWidths { name := "output" } ∧
                                          Option.isSome
                                              (Buffer.get! (Map.get! st.buffers { name := "output" })
                                                (st.cycle - Back.toNat 0, 0)) =
                                            true then
                                  some
                                    (Lit.Val
                                      (Option.get!
                                        (Buffer.get! (Map.get! st.buffers { name := "output" })
                                          (st.cycle - Back.toNat 0, 0))))
                                else none)
                              { name := "1" }) -
                          Option.get!
                            (State.felts
                              (st["output[0]"] ←ₛ
                                if
                                    0 ≤ st.cycle ∧
                                      { name := "output" } ∈ st.vars ∧
                                        0 < Map.get! st.bufferWidths { name := "output" } ∧
                                          Option.isSome
                                              (Buffer.get! (Map.get! st.buffers { name := "output" })
                                                (st.cycle - Back.toNat 0, 0)) =
                                            true then
                                  some
                                    (Lit.Val
                                      (Option.get!
                                        (Buffer.get! (Map.get! st.buffers { name := "output" })
                                          (st.cycle - Back.toNat 0, 0))))
                                else none)
                              { name := "output[0]" })))
                      { name := "1 - Output[0]" }) =
                  0) ::
              (st["output[0]"] ←ₛ
                  if
                      0 ≤ st.cycle ∧
                        { name := "output" } ∈ st.vars ∧
                          0 < Map.get! st.bufferWidths { name := "output" } ∧
                            Option.isSome
                                (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 0)) =
                              true then
                    some
                      (Lit.Val
                        (Option.get!
                          (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 0))))
                  else none).constraints,
          cycle :=
            (st["output[0]"] ←ₛ
                if
                    0 ≤ st.cycle ∧
                      { name := "output" } ∈ st.vars ∧
                        0 < Map.get! st.bufferWidths { name := "output" } ∧
                          Option.isSome
                              (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 0)) =
                            true then
                  some
                    (Lit.Val
                      (Option.get!
                        (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 0))))
                else none).cycle,
          felts :=
            (State.updateFelts
                (State.updateFelts
                  (st["output[0]"] ←ₛ
                    if
                        0 ≤ st.cycle ∧
                          { name := "output" } ∈ st.vars ∧
                            0 < Map.get! st.bufferWidths { name := "output" } ∧
                              Option.isSome
                                  (Buffer.get! (Map.get! st.buffers { name := "output" })
                                    (st.cycle - Back.toNat 0, 0)) =
                                true then
                      some
                        (Lit.Val
                          (Option.get!
                            (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 0))))
                    else none)
                  { name := "1 - Output[0]" }
                  (Option.get!
                      (State.felts
                        (st["output[0]"] ←ₛ
                          if
                              0 ≤ st.cycle ∧
                                { name := "output" } ∈ st.vars ∧
                                  0 < Map.get! st.bufferWidths { name := "output" } ∧
                                    Option.isSome
                                        (Buffer.get! (Map.get! st.buffers { name := "output" })
                                          (st.cycle - Back.toNat 0, 0)) =
                                      true then
                            some
                              (Lit.Val
                                (Option.get!
                                  (Buffer.get! (Map.get! st.buffers { name := "output" })
                                    (st.cycle - Back.toNat 0, 0))))
                          else none)
                        { name := "1" }) -
                    Option.get!
                      (State.felts
                        (st["output[0]"] ←ₛ
                          if
                              0 ≤ st.cycle ∧
                                { name := "output" } ∈ st.vars ∧
                                  0 < Map.get! st.bufferWidths { name := "output" } ∧
                                    Option.isSome
                                        (Buffer.get! (Map.get! st.buffers { name := "output" })
                                          (st.cycle - Back.toNat 0, 0)) =
                                      true then
                            some
                              (Lit.Val
                                (Option.get!
                                  (Buffer.get! (Map.get! st.buffers { name := "output" })
                                    (st.cycle - Back.toNat 0, 0))))
                          else none)
                        { name := "output[0]" })))
                { name := "output[0] <= 1" }
                (Option.get!
                    (State.felts
                      (State.updateFelts
                        (st["output[0]"] ←ₛ
                          if
                              0 ≤ st.cycle ∧
                                { name := "output" } ∈ st.vars ∧
                                  0 < Map.get! st.bufferWidths { name := "output" } ∧
                                    Option.isSome
                                        (Buffer.get! (Map.get! st.buffers { name := "output" })
                                          (st.cycle - Back.toNat 0, 0)) =
                                      true then
                            some
                              (Lit.Val
                                (Option.get!
                                  (Buffer.get! (Map.get! st.buffers { name := "output" })
                                    (st.cycle - Back.toNat 0, 0))))
                          else none)
                        { name := "1 - Output[0]" }
                        (Option.get!
                            (State.felts
                              (st["output[0]"] ←ₛ
                                if
                                    0 ≤ st.cycle ∧
                                      { name := "output" } ∈ st.vars ∧
                                        0 < Map.get! st.bufferWidths { name := "output" } ∧
                                          Option.isSome
                                              (Buffer.get! (Map.get! st.buffers { name := "output" })
                                                (st.cycle - Back.toNat 0, 0)) =
                                            true then
                                  some
                                    (Lit.Val
                                      (Option.get!
                                        (Buffer.get! (Map.get! st.buffers { name := "output" })
                                          (st.cycle - Back.toNat 0, 0))))
                                else none)
                              { name := "1" }) -
                          Option.get!
                            (State.felts
                              (st["output[0]"] ←ₛ
                                if
                                    0 ≤ st.cycle ∧
                                      { name := "output" } ∈ st.vars ∧
                                        0 < Map.get! st.bufferWidths { name := "output" } ∧
                                          Option.isSome
                                              (Buffer.get! (Map.get! st.buffers { name := "output" })
                                                (st.cycle - Back.toNat 0, 0)) =
                                            true then
                                  some
                                    (Lit.Val
                                      (Option.get!
                                        (Buffer.get! (Map.get! st.buffers { name := "output" })
                                          (st.cycle - Back.toNat 0, 0))))
                                else none)
                              { name := "output[0]" })))
                      { name := "output[0]" }) *
                  Option.get!
                    (State.felts
                      (State.updateFelts
                        (st["output[0]"] ←ₛ
                          if
                              0 ≤ st.cycle ∧
                                { name := "output" } ∈ st.vars ∧
                                  0 < Map.get! st.bufferWidths { name := "output" } ∧
                                    Option.isSome
                                        (Buffer.get! (Map.get! st.buffers { name := "output" })
                                          (st.cycle - Back.toNat 0, 0)) =
                                      true then
                            some
                              (Lit.Val
                                (Option.get!
                                  (Buffer.get! (Map.get! st.buffers { name := "output" })
                                    (st.cycle - Back.toNat 0, 0))))
                          else none)
                        { name := "1 - Output[0]" }
                        (Option.get!
                            (State.felts
                              (st["output[0]"] ←ₛ
                                if
                                    0 ≤ st.cycle ∧
                                      { name := "output" } ∈ st.vars ∧
                                        0 < Map.get! st.bufferWidths { name := "output" } ∧
                                          Option.isSome
                                              (Buffer.get! (Map.get! st.buffers { name := "output" })
                                                (st.cycle - Back.toNat 0, 0)) =
                                            true then
                                  some
                                    (Lit.Val
                                      (Option.get!
                                        (Buffer.get! (Map.get! st.buffers { name := "output" })
                                          (st.cycle - Back.toNat 0, 0))))
                                else none)
                              { name := "1" }) -
                          Option.get!
                            (State.felts
                              (st["output[0]"] ←ₛ
                                if
                                    0 ≤ st.cycle ∧
                                      { name := "output" } ∈ st.vars ∧
                                        0 < Map.get! st.bufferWidths { name := "output" } ∧
                                          Option.isSome
                                              (Buffer.get! (Map.get! st.buffers { name := "output" })
                                                (st.cycle - Back.toNat 0, 0)) =
                                            true then
                                  some
                                    (Lit.Val
                                      (Option.get!
                                        (Buffer.get! (Map.get! st.buffers { name := "output" })
                                          (st.cycle - Back.toNat 0, 0))))
                                else none)
                              { name := "output[0]" })))
                      { name := "1 - Output[0]" }))).felts,
          isFailed :=
            (st["output[0]"] ←ₛ
                if
                    0 ≤ st.cycle ∧
                      { name := "output" } ∈ st.vars ∧
                        0 < Map.get! st.bufferWidths { name := "output" } ∧
                          Option.isSome
                              (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 0)) =
                            true then
                  some
                    (Lit.Val
                      (Option.get!
                        (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 0))))
                else none).isFailed,
          props :=
            (st["output[0]"] ←ₛ
                if
                    0 ≤ st.cycle ∧
                      { name := "output" } ∈ st.vars ∧
                        0 < Map.get! st.bufferWidths { name := "output" } ∧
                          Option.isSome
                              (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 0)) =
                            true then
                  some
                    (Lit.Val
                      (Option.get!
                        (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 0))))
                else none).props,
          vars :=
            (st["output[0]"] ←ₛ
                if
                    0 ≤ st.cycle ∧
                      { name := "output" } ∈ st.vars ∧
                        0 < Map.get! st.bufferWidths { name := "output" } ∧
                          Option.isSome
                              (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 0)) =
                            true then
                  some
                    (Lit.Val
                      (Option.get!
                        (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 0))))
                else none).vars }

-- Run the program from part₅ onwards by using part₅_state rather than Code.part₅
def part₅_state_update (st: State): State :=
  Γ (part₅_state st) ⟦Code.part₆; Code.part₇; Code.part₈⟧

-- Prove that substituting part₅_state for Code.part₅ produces the same result
-- ****************************** WEAKEST PRE - Part₅ ******************************
lemma part₅_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  (MLIR.runProgram (Code.part₅; Code.part₆; Code.part₇; Code.part₈) st).lastOutput = [y₁, y₂, y₃] ↔
  (part₅_state_update st).lastOutput = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₆; Code.part₇; Code.part₈) = prog
  unfold Code.part₅
  MLIR
  rewrite [←eq]
  unfold part₅_state_update part₅_state
  rfl
-- ****************************** WEAKEST PRE - Part₅ ******************************

lemma part₅_updates_opaque {st : State} : 
  (part₄_state_update st).lastOutput = [y₁, y₂, y₃] ↔
  (part₅_state_update (part₄_state st)).lastOutput = [y₁, y₂, y₃] := by
  simp [part₄_state_update, part₅_wp]

end Risc0.OneHot.Witness.WP
