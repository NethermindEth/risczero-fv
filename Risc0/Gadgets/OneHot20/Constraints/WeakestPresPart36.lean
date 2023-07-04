import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart35

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part36 on st
def part36_state (st: State) : State :=
  
        ((((st[props][{ name := "%144" }] ←
                (Option.get! (State.props st { name := "%140" }) ∧
                  Option.get! (State.felts st { name := "%143" }) = 0))[felts][{ name := "%145" }] ←
              Option.get! (State.felts st { name := "%141" }) +
                Option.get! (State.felts st { name := "%64" }))[felts][{ name := "%146" }] ←
            Option.get! (State.felts st { name := "%0" }) -
              Option.get! (State.felts st { name := "%67" }))[felts][{ name := "%147" }] ←
          Option.get! (State.felts st { name := "%67" }) *
            (Option.get! (State.felts st { name := "%0" }) - Option.get! (State.felts st { name := "%67" }))) 

def part36_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%64"⟩) ⟨"%141"⟩) ⟨"%143"⟩) ⟨"%146"⟩

-- Run the program from part36 onwards by using part36_state rather than Code.part36
def part36_state_update (st: State): State :=
  Γ (part36_drops (part36_state st)) ⟦Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%19"⟩;dropfelt ⟨"%73"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%108"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%120"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%132"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%140"⟩;dropfelt ⟨"%144"⟩;dropfelt ⟨"%148"⟩;dropfelt ⟨"%152"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;dropfelt ⟨"%159"⟩⟧

-- Prove that substituting part36_state for Code.part36 produces the same result
lemma part36_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%19"⟩;dropfelt ⟨"%73"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%108"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%120"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%132"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%140"⟩;dropfelt ⟨"%144"⟩;dropfelt ⟨"%148"⟩;dropfelt ⟨"%152"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;dropfelt ⟨"%159"⟩) st) ↔
  Code.getReturn (part36_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%19"⟩;dropfelt ⟨"%73"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%108"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%120"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%132"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%140"⟩;dropfelt ⟨"%144"⟩;dropfelt ⟨"%148"⟩;dropfelt ⟨"%152"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;dropfelt ⟨"%159"⟩) = prog
  unfold Code.part36
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part36_state_update part36_drops part36_state
  rfl

lemma part36_updates_opaque {st : State} : 
  Code.getReturn (part35_state_update st) ↔
  Code.getReturn (part36_state_update (part35_drops (part35_state st))) := by
  simp [part35_state_update, part36_wp]

lemma part36_cumulative_wp {x0 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19: Felt} :
  Code.run (start_state [x0] ([y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19])) ↔
  Code.getReturn
      (part36_state_update
        ((((((((((((((((((((((((({
                                                            buffers :=
                                                              ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                                                                  [[some y0, some y1, some y2, some y3, some y4,
                                                                      some y5, some y6, some y7, some y8, some y9,
                                                                      some y10, some y11, some y12, some y13, some y14,
                                                                      some y15, some y16, some y17, some y18,
                                                                      some y19]])[{ name := "code" }] ←ₘ
                                                                [[some x0]],
                                                            bufferWidths :=
                                                              ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                                                                  20)[{ name := "code" }] ←ₘ
                                                                1,
                                                            constraints := [], cycle := 0, felts := Map.empty,
                                                            isFailed := false, props := Map.empty,
                                                            vars :=
                                                              [{ name := "code" },
                                                                { name := "data" }] }[props][{ name := "%19" }] ←
                                                          True)[felts][{ name := "%64" }] ←
                                                        y16)[felts][{ name := "%67" }] ←
                                                      y17)[felts][{ name := "%70" }] ←
                                                    y18)[felts][{ name := "%73" }] ←
                                                  y19)[props][{ name := "%77" }] ←
                                                y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 +
                                                                          y9 * 9 +
                                                                        y10 * 10 +
                                                                      y11 * 11 +
                                                                    y12 * 12 +
                                                                  y13 * 13 +
                                                                y14 * 14 +
                                                              y15 * 15 +
                                                            y16 * 16 +
                                                          y17 * 17 +
                                                        y18 * 18 +
                                                      y19 * 19 -
                                                    x0 =
                                                  0)[felts][{ name := "%0" }] ←
                                              1)[props][{ name := "%81" }] ←
                                            (y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 +
                                                                        y9 * 9 +
                                                                      y10 * 10 +
                                                                    y11 * 11 +
                                                                  y12 * 12 +
                                                                y13 * 13 +
                                                              y14 * 14 +
                                                            y15 * 15 +
                                                          y16 * 16 +
                                                        y17 * 17 +
                                                      y18 * 18 +
                                                    y19 * 19 -
                                                  x0 =
                                                0 ∧
                                              (y0 = 0 ∨ 1 - y0 = 0)))[props][{ name := "%84" }] ←
                                          ((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 +
                                                                      y10 * 10 +
                                                                    y11 * 11 +
                                                                  y12 * 12 +
                                                                y13 * 13 +
                                                              y14 * 14 +
                                                            y15 * 15 +
                                                          y16 * 16 +
                                                        y17 * 17 +
                                                      y18 * 18 +
                                                    y19 * 19 -
                                                  x0 =
                                                0 ∧
                                              (y0 = 0 ∨ 1 - y0 = 0)) ∧
                                            (y1 = 0 ∨ 1 - y1 = 0)))[props][{ name := "%88" }] ←
                                        (((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 +
                                                                      y10 * 10 +
                                                                    y11 * 11 +
                                                                  y12 * 12 +
                                                                y13 * 13 +
                                                              y14 * 14 +
                                                            y15 * 15 +
                                                          y16 * 16 +
                                                        y17 * 17 +
                                                      y18 * 18 +
                                                    y19 * 19 -
                                                  x0 =
                                                0 ∧
                                              (y0 = 0 ∨ 1 - y0 = 0)) ∧
                                            (y1 = 0 ∨ 1 - y1 = 0)) ∧
                                          (y2 = 0 ∨ 1 - y2 = 0)))[props][{ name := "%92" }] ←
                                      ((((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 +
                                                                      y10 * 10 +
                                                                    y11 * 11 +
                                                                  y12 * 12 +
                                                                y13 * 13 +
                                                              y14 * 14 +
                                                            y15 * 15 +
                                                          y16 * 16 +
                                                        y17 * 17 +
                                                      y18 * 18 +
                                                    y19 * 19 -
                                                  x0 =
                                                0 ∧
                                              (y0 = 0 ∨ 1 - y0 = 0)) ∧
                                            (y1 = 0 ∨ 1 - y1 = 0)) ∧
                                          (y2 = 0 ∨ 1 - y2 = 0)) ∧
                                        (y3 = 0 ∨ 1 - y3 = 0)))[props][{ name := "%96" }] ←
                                    (((((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 +
                                                                      y10 * 10 +
                                                                    y11 * 11 +
                                                                  y12 * 12 +
                                                                y13 * 13 +
                                                              y14 * 14 +
                                                            y15 * 15 +
                                                          y16 * 16 +
                                                        y17 * 17 +
                                                      y18 * 18 +
                                                    y19 * 19 -
                                                  x0 =
                                                0 ∧
                                              (y0 = 0 ∨ 1 - y0 = 0)) ∧
                                            (y1 = 0 ∨ 1 - y1 = 0)) ∧
                                          (y2 = 0 ∨ 1 - y2 = 0)) ∧
                                        (y3 = 0 ∨ 1 - y3 = 0)) ∧
                                      (y4 = 0 ∨ 1 - y4 = 0)))[props][{ name := "%100" }] ←
                                  ((((((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 +
                                                                      y10 * 10 +
                                                                    y11 * 11 +
                                                                  y12 * 12 +
                                                                y13 * 13 +
                                                              y14 * 14 +
                                                            y15 * 15 +
                                                          y16 * 16 +
                                                        y17 * 17 +
                                                      y18 * 18 +
                                                    y19 * 19 -
                                                  x0 =
                                                0 ∧
                                              (y0 = 0 ∨ 1 - y0 = 0)) ∧
                                            (y1 = 0 ∨ 1 - y1 = 0)) ∧
                                          (y2 = 0 ∨ 1 - y2 = 0)) ∧
                                        (y3 = 0 ∨ 1 - y3 = 0)) ∧
                                      (y4 = 0 ∨ 1 - y4 = 0)) ∧
                                    (y5 = 0 ∨ 1 - y5 = 0)))[props][{ name := "%104" }] ←
                                (((((((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 +
                                                                      y10 * 10 +
                                                                    y11 * 11 +
                                                                  y12 * 12 +
                                                                y13 * 13 +
                                                              y14 * 14 +
                                                            y15 * 15 +
                                                          y16 * 16 +
                                                        y17 * 17 +
                                                      y18 * 18 +
                                                    y19 * 19 -
                                                  x0 =
                                                0 ∧
                                              (y0 = 0 ∨ 1 - y0 = 0)) ∧
                                            (y1 = 0 ∨ 1 - y1 = 0)) ∧
                                          (y2 = 0 ∨ 1 - y2 = 0)) ∧
                                        (y3 = 0 ∨ 1 - y3 = 0)) ∧
                                      (y4 = 0 ∨ 1 - y4 = 0)) ∧
                                    (y5 = 0 ∨ 1 - y5 = 0)) ∧
                                  (y6 = 0 ∨ 1 - y6 = 0)))[props][{ name := "%108" }] ←
                              ((((((((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 +
                                                                      y10 * 10 +
                                                                    y11 * 11 +
                                                                  y12 * 12 +
                                                                y13 * 13 +
                                                              y14 * 14 +
                                                            y15 * 15 +
                                                          y16 * 16 +
                                                        y17 * 17 +
                                                      y18 * 18 +
                                                    y19 * 19 -
                                                  x0 =
                                                0 ∧
                                              (y0 = 0 ∨ 1 - y0 = 0)) ∧
                                            (y1 = 0 ∨ 1 - y1 = 0)) ∧
                                          (y2 = 0 ∨ 1 - y2 = 0)) ∧
                                        (y3 = 0 ∨ 1 - y3 = 0)) ∧
                                      (y4 = 0 ∨ 1 - y4 = 0)) ∧
                                    (y5 = 0 ∨ 1 - y5 = 0)) ∧
                                  (y6 = 0 ∨ 1 - y6 = 0)) ∧
                                (y7 = 0 ∨ 1 - y7 = 0)))[props][{ name := "%112" }] ←
                            (((((((((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 +
                                                                      y10 * 10 +
                                                                    y11 * 11 +
                                                                  y12 * 12 +
                                                                y13 * 13 +
                                                              y14 * 14 +
                                                            y15 * 15 +
                                                          y16 * 16 +
                                                        y17 * 17 +
                                                      y18 * 18 +
                                                    y19 * 19 -
                                                  x0 =
                                                0 ∧
                                              (y0 = 0 ∨ 1 - y0 = 0)) ∧
                                            (y1 = 0 ∨ 1 - y1 = 0)) ∧
                                          (y2 = 0 ∨ 1 - y2 = 0)) ∧
                                        (y3 = 0 ∨ 1 - y3 = 0)) ∧
                                      (y4 = 0 ∨ 1 - y4 = 0)) ∧
                                    (y5 = 0 ∨ 1 - y5 = 0)) ∧
                                  (y6 = 0 ∨ 1 - y6 = 0)) ∧
                                (y7 = 0 ∨ 1 - y7 = 0)) ∧
                              (y8 = 0 ∨ 1 - y8 = 0)))[props][{ name := "%116" }] ←
                          ((((((((((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 +
                                                                      y10 * 10 +
                                                                    y11 * 11 +
                                                                  y12 * 12 +
                                                                y13 * 13 +
                                                              y14 * 14 +
                                                            y15 * 15 +
                                                          y16 * 16 +
                                                        y17 * 17 +
                                                      y18 * 18 +
                                                    y19 * 19 -
                                                  x0 =
                                                0 ∧
                                              (y0 = 0 ∨ 1 - y0 = 0)) ∧
                                            (y1 = 0 ∨ 1 - y1 = 0)) ∧
                                          (y2 = 0 ∨ 1 - y2 = 0)) ∧
                                        (y3 = 0 ∨ 1 - y3 = 0)) ∧
                                      (y4 = 0 ∨ 1 - y4 = 0)) ∧
                                    (y5 = 0 ∨ 1 - y5 = 0)) ∧
                                  (y6 = 0 ∨ 1 - y6 = 0)) ∧
                                (y7 = 0 ∨ 1 - y7 = 0)) ∧
                              (y8 = 0 ∨ 1 - y8 = 0)) ∧
                            (y9 = 0 ∨ 1 - y9 = 0)))[props][{ name := "%120" }] ←
                        (((((((((((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 +
                                                                      y10 * 10 +
                                                                    y11 * 11 +
                                                                  y12 * 12 +
                                                                y13 * 13 +
                                                              y14 * 14 +
                                                            y15 * 15 +
                                                          y16 * 16 +
                                                        y17 * 17 +
                                                      y18 * 18 +
                                                    y19 * 19 -
                                                  x0 =
                                                0 ∧
                                              (y0 = 0 ∨ 1 - y0 = 0)) ∧
                                            (y1 = 0 ∨ 1 - y1 = 0)) ∧
                                          (y2 = 0 ∨ 1 - y2 = 0)) ∧
                                        (y3 = 0 ∨ 1 - y3 = 0)) ∧
                                      (y4 = 0 ∨ 1 - y4 = 0)) ∧
                                    (y5 = 0 ∨ 1 - y5 = 0)) ∧
                                  (y6 = 0 ∨ 1 - y6 = 0)) ∧
                                (y7 = 0 ∨ 1 - y7 = 0)) ∧
                              (y8 = 0 ∨ 1 - y8 = 0)) ∧
                            (y9 = 0 ∨ 1 - y9 = 0)) ∧
                          (y10 = 0 ∨ 1 - y10 = 0)))[props][{ name := "%124" }] ←
                      ((((((((((((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 +
                                                                      y10 * 10 +
                                                                    y11 * 11 +
                                                                  y12 * 12 +
                                                                y13 * 13 +
                                                              y14 * 14 +
                                                            y15 * 15 +
                                                          y16 * 16 +
                                                        y17 * 17 +
                                                      y18 * 18 +
                                                    y19 * 19 -
                                                  x0 =
                                                0 ∧
                                              (y0 = 0 ∨ 1 - y0 = 0)) ∧
                                            (y1 = 0 ∨ 1 - y1 = 0)) ∧
                                          (y2 = 0 ∨ 1 - y2 = 0)) ∧
                                        (y3 = 0 ∨ 1 - y3 = 0)) ∧
                                      (y4 = 0 ∨ 1 - y4 = 0)) ∧
                                    (y5 = 0 ∨ 1 - y5 = 0)) ∧
                                  (y6 = 0 ∨ 1 - y6 = 0)) ∧
                                (y7 = 0 ∨ 1 - y7 = 0)) ∧
                              (y8 = 0 ∨ 1 - y8 = 0)) ∧
                            (y9 = 0 ∨ 1 - y9 = 0)) ∧
                          (y10 = 0 ∨ 1 - y10 = 0)) ∧
                        (y11 = 0 ∨ 1 - y11 = 0)))[props][{ name := "%128" }] ←
                    (((((((((((((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 + y10 * 10 +
                                                                    y11 * 11 +
                                                                  y12 * 12 +
                                                                y13 * 13 +
                                                              y14 * 14 +
                                                            y15 * 15 +
                                                          y16 * 16 +
                                                        y17 * 17 +
                                                      y18 * 18 +
                                                    y19 * 19 -
                                                  x0 =
                                                0 ∧
                                              (y0 = 0 ∨ 1 - y0 = 0)) ∧
                                            (y1 = 0 ∨ 1 - y1 = 0)) ∧
                                          (y2 = 0 ∨ 1 - y2 = 0)) ∧
                                        (y3 = 0 ∨ 1 - y3 = 0)) ∧
                                      (y4 = 0 ∨ 1 - y4 = 0)) ∧
                                    (y5 = 0 ∨ 1 - y5 = 0)) ∧
                                  (y6 = 0 ∨ 1 - y6 = 0)) ∧
                                (y7 = 0 ∨ 1 - y7 = 0)) ∧
                              (y8 = 0 ∨ 1 - y8 = 0)) ∧
                            (y9 = 0 ∨ 1 - y9 = 0)) ∧
                          (y10 = 0 ∨ 1 - y10 = 0)) ∧
                        (y11 = 0 ∨ 1 - y11 = 0)) ∧
                      (y12 = 0 ∨ 1 - y12 = 0)))[props][{ name := "%132" }] ←
                  ((((((((((((((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 + y10 * 10 +
                                                                    y11 * 11 +
                                                                  y12 * 12 +
                                                                y13 * 13 +
                                                              y14 * 14 +
                                                            y15 * 15 +
                                                          y16 * 16 +
                                                        y17 * 17 +
                                                      y18 * 18 +
                                                    y19 * 19 -
                                                  x0 =
                                                0 ∧
                                              (y0 = 0 ∨ 1 - y0 = 0)) ∧
                                            (y1 = 0 ∨ 1 - y1 = 0)) ∧
                                          (y2 = 0 ∨ 1 - y2 = 0)) ∧
                                        (y3 = 0 ∨ 1 - y3 = 0)) ∧
                                      (y4 = 0 ∨ 1 - y4 = 0)) ∧
                                    (y5 = 0 ∨ 1 - y5 = 0)) ∧
                                  (y6 = 0 ∨ 1 - y6 = 0)) ∧
                                (y7 = 0 ∨ 1 - y7 = 0)) ∧
                              (y8 = 0 ∨ 1 - y8 = 0)) ∧
                            (y9 = 0 ∨ 1 - y9 = 0)) ∧
                          (y10 = 0 ∨ 1 - y10 = 0)) ∧
                        (y11 = 0 ∨ 1 - y11 = 0)) ∧
                      (y12 = 0 ∨ 1 - y12 = 0)) ∧
                    (y13 = 0 ∨ 1 - y13 = 0)))[props][{ name := "%136" }] ←
                (((((((((((((((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 + y10 * 10 +
                                                                    y11 * 11 +
                                                                  y12 * 12 +
                                                                y13 * 13 +
                                                              y14 * 14 +
                                                            y15 * 15 +
                                                          y16 * 16 +
                                                        y17 * 17 +
                                                      y18 * 18 +
                                                    y19 * 19 -
                                                  x0 =
                                                0 ∧
                                              (y0 = 0 ∨ 1 - y0 = 0)) ∧
                                            (y1 = 0 ∨ 1 - y1 = 0)) ∧
                                          (y2 = 0 ∨ 1 - y2 = 0)) ∧
                                        (y3 = 0 ∨ 1 - y3 = 0)) ∧
                                      (y4 = 0 ∨ 1 - y4 = 0)) ∧
                                    (y5 = 0 ∨ 1 - y5 = 0)) ∧
                                  (y6 = 0 ∨ 1 - y6 = 0)) ∧
                                (y7 = 0 ∨ 1 - y7 = 0)) ∧
                              (y8 = 0 ∨ 1 - y8 = 0)) ∧
                            (y9 = 0 ∨ 1 - y9 = 0)) ∧
                          (y10 = 0 ∨ 1 - y10 = 0)) ∧
                        (y11 = 0 ∨ 1 - y11 = 0)) ∧
                      (y12 = 0 ∨ 1 - y12 = 0)) ∧
                    (y13 = 0 ∨ 1 - y13 = 0)) ∧
                  (y14 = 0 ∨ 1 - y14 = 0)))[props][{ name := "%140" }] ←
              ((((((((((((((((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 + y10 * 10 +
                                                                    y11 * 11 +
                                                                  y12 * 12 +
                                                                y13 * 13 +
                                                              y14 * 14 +
                                                            y15 * 15 +
                                                          y16 * 16 +
                                                        y17 * 17 +
                                                      y18 * 18 +
                                                    y19 * 19 -
                                                  x0 =
                                                0 ∧
                                              (y0 = 0 ∨ 1 - y0 = 0)) ∧
                                            (y1 = 0 ∨ 1 - y1 = 0)) ∧
                                          (y2 = 0 ∨ 1 - y2 = 0)) ∧
                                        (y3 = 0 ∨ 1 - y3 = 0)) ∧
                                      (y4 = 0 ∨ 1 - y4 = 0)) ∧
                                    (y5 = 0 ∨ 1 - y5 = 0)) ∧
                                  (y6 = 0 ∨ 1 - y6 = 0)) ∧
                                (y7 = 0 ∨ 1 - y7 = 0)) ∧
                              (y8 = 0 ∨ 1 - y8 = 0)) ∧
                            (y9 = 0 ∨ 1 - y9 = 0)) ∧
                          (y10 = 0 ∨ 1 - y10 = 0)) ∧
                        (y11 = 0 ∨ 1 - y11 = 0)) ∧
                      (y12 = 0 ∨ 1 - y12 = 0)) ∧
                    (y13 = 0 ∨ 1 - y13 = 0)) ∧
                  (y14 = 0 ∨ 1 - y14 = 0)) ∧
                (y15 = 0 ∨ 1 - y15 = 0)))[felts][{ name := "%141" }] ←
            y0 + y1 + y2 + y3 + y4 + y5 + y6 + y7 + y8 + y9 + y10 + y11 + y12 + y13 + y14 +
              y15)[felts][{ name := "%143" }] ←
          y16 * (1 - y16)))  := by
    rewrite [part35_cumulative_wp]
    rewrite [part36_updates_opaque]
    unfold part35_state
    MLIR_states_updates'
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates'
    unfold part35_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

end Risc0.OneHot20.Constraints.WP