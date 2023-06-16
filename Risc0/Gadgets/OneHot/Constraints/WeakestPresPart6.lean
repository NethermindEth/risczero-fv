import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Constraints.Code
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart5

namespace Risc0.OneHot.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part₆ on st
def part₆_state (st: State) : State := {
  buffers := st.buffers, bufferWidths := st.bufferWidths, constraints := st.constraints, cycle := st.cycle,
      felts :=
        (State.updateFelts
            (State.updateFelts
              { buffers := st.buffers, bufferWidths := st.bufferWidths, constraints := st.constraints,
                cycle := st.cycle, felts := st.felts, isFailed := st.isFailed,
                props :=
                  st.props[{ name := "andEqz output[2]<=1" }] ←ₘ
                    (Option.get! (State.props st { name := "andEqz output[1]<=1" }) ∧
                      Option.get! (State.felts st { name := "output[2]<=1" }) = 0),
                vars := st.vars }
              { name := "outputSum" }
              (Option.get! (State.felts st { name := "output[0]+Output[1]" }) +
                Option.get! (State.felts st { name := "output[2]" })))
            { name := "outputSum-1" }
            (Option.get!
                (State.felts
                  (State.updateFelts
                    { buffers := st.buffers, bufferWidths := st.bufferWidths, constraints := st.constraints,
                      cycle := st.cycle, felts := st.felts, isFailed := st.isFailed,
                      props :=
                        st.props[{ name := "andEqz output[2]<=1" }] ←ₘ
                          (Option.get! (State.props st { name := "andEqz output[1]<=1" }) ∧
                            Option.get! (State.felts st { name := "output[2]<=1" }) = 0),
                      vars := st.vars }
                    { name := "outputSum" }
                    (Option.get! (State.felts st { name := "output[0]+Output[1]" }) +
                      Option.get! (State.felts st { name := "output[2]" })))
                  { name := "outputSum" }) -
              Option.get!
                (State.felts
                  (State.updateFelts
                    { buffers := st.buffers, bufferWidths := st.bufferWidths, constraints := st.constraints,
                      cycle := st.cycle, felts := st.felts, isFailed := st.isFailed,
                      props :=
                        st.props[{ name := "andEqz output[2]<=1" }] ←ₘ
                          (Option.get! (State.props st { name := "andEqz output[1]<=1" }) ∧
                            Option.get! (State.felts st { name := "output[2]<=1" }) = 0),
                      vars := st.vars }
                    { name := "outputSum" }
                    (Option.get! (State.felts st { name := "output[0]+Output[1]" }) +
                      Option.get! (State.felts st { name := "output[2]" })))
                  { name := "1" }))).felts,
      isFailed := st.isFailed,
      props :=
        (st.props[{ name := "andEqz output[2]<=1" }] ←ₘ
            (Option.get! (State.props st { name := "andEqz output[1]<=1" }) ∧
              Option.get! (State.felts st { name := "output[2]<=1" }) = 0))[{ name := "andEqz outputSum-1" }] ←ₘ
          (Option.get!
              ((st.props[{ name := "andEqz output[2]<=1" }] ←ₘ
                  (Option.get! (State.props st { name := "andEqz output[1]<=1" }) ∧
                    Option.get! (State.felts st { name := "output[2]<=1" }) = 0))
                { name := "andEqz output[2]<=1" }) ∧
            Option.get!
                (State.felts
                  (State.updateFelts
                    (State.updateFelts
                      { buffers := st.buffers, bufferWidths := st.bufferWidths, constraints := st.constraints,
                        cycle := st.cycle, felts := st.felts, isFailed := st.isFailed,
                        props :=
                          st.props[{ name := "andEqz output[2]<=1" }] ←ₘ
                            (Option.get! (State.props st { name := "andEqz output[1]<=1" }) ∧
                              Option.get! (State.felts st { name := "output[2]<=1" }) = 0),
                        vars := st.vars }
                      { name := "outputSum" }
                      (Option.get! (State.felts st { name := "output[0]+Output[1]" }) +
                        Option.get! (State.felts st { name := "output[2]" })))
                    { name := "outputSum-1" }
                    (Option.get!
                        (State.felts
                          (State.updateFelts
                            { buffers := st.buffers, bufferWidths := st.bufferWidths, constraints := st.constraints,
                              cycle := st.cycle, felts := st.felts, isFailed := st.isFailed,
                              props :=
                                st.props[{ name := "andEqz output[2]<=1" }] ←ₘ
                                  (Option.get! (State.props st { name := "andEqz output[1]<=1" }) ∧
                                    Option.get! (State.felts st { name := "output[2]<=1" }) = 0),
                              vars := st.vars }
                            { name := "outputSum" }
                            (Option.get! (State.felts st { name := "output[0]+Output[1]" }) +
                              Option.get! (State.felts st { name := "output[2]" })))
                          { name := "outputSum" }) -
                      Option.get!
                        (State.felts
                          (State.updateFelts
                            { buffers := st.buffers, bufferWidths := st.bufferWidths, constraints := st.constraints,
                              cycle := st.cycle, felts := st.felts, isFailed := st.isFailed,
                              props :=
                                st.props[{ name := "andEqz output[2]<=1" }] ←ₘ
                                  (Option.get! (State.props st { name := "andEqz output[1]<=1" }) ∧
                                    Option.get! (State.felts st { name := "output[2]<=1" }) = 0),
                              vars := st.vars }
                            { name := "outputSum" }
                            (Option.get! (State.felts st { name := "output[0]+Output[1]" }) +
                              Option.get! (State.felts st { name := "output[2]" })))
                          { name := "1" })))
                  { name := "outputSum-1" }) =
              0),
      vars := st.vars }

-- Run the whole program by using part₆_state rather than Code.part₆
def part₆_state_update (st: State): State :=
  part₆_state st

-- Prove that substituting part₆_state for Code.part₆ produces the same result
-- ****************************** WEAKEST PRE - Part₆ ******************************
lemma part₆_wp {st : State} :
  Code.getReturn (MLIR.runProgram Code.part₆ st) ↔
  Code.getReturn (part₆_state_update st) := by
  unfold MLIR.runProgram; simp only
  unfold Code.part₆
  MLIR
  unfold part₆_state_update part₆_state
  rfl
-- ****************************** WEAKEST PRE - Part₆ ******************************

lemma part₆_updates_opaque {st : State} : 
  Code.getReturn (part₅_state_update st) ↔
  Code.getReturn (part₆_state_update (part₅_state st)) := by
  simp [part₅_state_update, part₆_wp]

end Risc0.OneHot.Constraints.WP
