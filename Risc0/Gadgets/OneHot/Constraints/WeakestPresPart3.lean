import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Constraints.Code
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart2

namespace Risc0.OneHot.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part₃ on st
def part₃_state (st: State) : State := State.updateFelts
        ({ buffers := st.buffers, bufferWidths := st.bufferWidths, constraints := st.constraints, cycle := st.cycle,
            felts :=
              (State.updateFelts st { name := "2*output[2]+output[1]-input" }
                  (Option.get! (State.felts st { name := "2*output[2]+output[1]" }) -
                    Option.get! (State.felts st { name := "input" }))).felts,
            isFailed := st.isFailed,
            props :=
              st.props[{ name := "andEqz 2*output[2]+output[1]-input" }] ←ₘ
                (Option.get! (State.props st { name := "true" }) ∧
                  Option.get!
                      (State.felts
                        (State.updateFelts st { name := "2*output[2]+output[1]-input" }
                          (Option.get! (State.felts st { name := "2*output[2]+output[1]" }) -
                            Option.get! (State.felts st { name := "input" })))
                        { name := "2*output[2]+output[1]-input" }) =
                    0),
            vars := st.vars }["output[0]"] ←ₛ
          if
              0 ≤ st.cycle ∧
                { name := "output" } ∈ st.vars ∧
                  0 < Map.get! st.bufferWidths { name := "output" } ∧
                    Option.isSome
                        (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 0)) =
                      true then
            some
              (Lit.Val
                (Option.get! (Buffer.get! (Map.get! st.buffers { name := "output" }) (st.cycle - Back.toNat 0, 0))))
          else none)
        { name := "1-Output[0]" }
        (Option.get!
            (State.felts
              ({ buffers := st.buffers, bufferWidths := st.bufferWidths, constraints := st.constraints,
                  cycle := st.cycle,
                  felts :=
                    (State.updateFelts st { name := "2*output[2]+output[1]-input" }
                        (Option.get! (State.felts st { name := "2*output[2]+output[1]" }) -
                          Option.get! (State.felts st { name := "input" }))).felts,
                  isFailed := st.isFailed,
                  props :=
                    st.props[{ name := "andEqz 2*output[2]+output[1]-input" }] ←ₘ
                      (Option.get! (State.props st { name := "true" }) ∧
                        Option.get!
                            (State.felts
                              (State.updateFelts st { name := "2*output[2]+output[1]-input" }
                                (Option.get! (State.felts st { name := "2*output[2]+output[1]" }) -
                                  Option.get! (State.felts st { name := "input" })))
                              { name := "2*output[2]+output[1]-input" }) =
                          0),
                  vars := st.vars }["output[0]"] ←ₛ
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
                else none)
              { name := "1" }) -
          Option.get!
            (State.felts
              ({ buffers := st.buffers, bufferWidths := st.bufferWidths, constraints := st.constraints,
                  cycle := st.cycle,
                  felts :=
                    (State.updateFelts st { name := "2*output[2]+output[1]-input" }
                        (Option.get! (State.felts st { name := "2*output[2]+output[1]" }) -
                          Option.get! (State.felts st { name := "input" }))).felts,
                  isFailed := st.isFailed,
                  props :=
                    st.props[{ name := "andEqz 2*output[2]+output[1]-input" }] ←ₘ
                      (Option.get! (State.props st { name := "true" }) ∧
                        Option.get!
                            (State.felts
                              (State.updateFelts st { name := "2*output[2]+output[1]-input" }
                                (Option.get! (State.felts st { name := "2*output[2]+output[1]" }) -
                                  Option.get! (State.felts st { name := "input" })))
                              { name := "2*output[2]+output[1]-input" }) =
                          0),
                  vars := st.vars }["output[0]"] ←ₛ
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
                else none)
              { name := "output[0]" }))

-- Run the whole program by using part₃_state rather than Code.part₃
def part₃_state_update (st: State): State :=
  Γ (part₃_state st) ⟦Code.part₄; Code.part₅; Code.part₆⟧

-- Prove that substituting part₃_state for Code.part₃ produces the same result
-- ****************************** WEAKEST PRE - Part₃ ******************************
lemma part₃_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part₃; Code.part₄; Code.part₅; Code.part₆) st) ↔
  Code.getReturn (part₃_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₄; Code.part₅; Code.part₆) = prog
  unfold Code.part₃
  MLIR
  unfold part₃_state_update part₃_state
  rewrite [←eq]
  rfl
-- ****************************** WEAKEST PRE - Part₃ ******************************

lemma part₃_updates_opaque {st : State} : 
  Code.getReturn (part₂_state_update st) ↔
  Code.getReturn (part₃_state_update (part₂_state st)) := by
  simp [part₂_state_update, part₃_wp]

end Risc0.OneHot.Constraints.WP
