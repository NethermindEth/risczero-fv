import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart28

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part29 on st
def part29_state (st: State) : State :=
  
        ((((st[props][{ name := "%116" }] ←
                (Option.get! (State.props st { name := "%112" }) ∧
                  Option.get! (State.felts st { name := "%115" }) = 0))[felts][{ name := "%117" }] ←
              Option.get! (State.felts st { name := "%113" }) +
                Option.get! (State.felts st { name := "%43" }))[felts][{ name := "%118" }] ←
            Option.get! (State.felts st { name := "%0" }) -
              Option.get! (State.felts st { name := "%46" }))[felts][{ name := "%119" }] ←
          Option.get! (State.felts st { name := "%46" }) *
            (Option.get! (State.felts st { name := "%0" }) - Option.get! (State.felts st { name := "%46" }))) 

def part29_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%43"⟩) ⟨"%113"⟩) ⟨"%115"⟩) ⟨"%118"⟩

-- Run the program from part29 onwards by using part29_state rather than Code.part29
def part29_state_update (st: State): State :=
  Γ (part29_drops (part29_state st)) ⟦Code.part30;dropfelt ⟨"%46"⟩;dropfelt ⟨"%117"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%122"⟩;Code.part31;dropfelt ⟨"%49"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%123"⟩;dropfelt ⟨"%126"⟩;Code.part32;dropfelt ⟨"%52"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%130"⟩;Code.part33;dropfelt ⟨"%55"⟩;dropfelt ⟨"%129"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%134"⟩;Code.part34;dropfelt ⟨"%58"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%135"⟩;dropfelt ⟨"%138"⟩;Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%19"⟩;dropfelt ⟨"%73"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%108"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%120"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%132"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%140"⟩;dropfelt ⟨"%144"⟩;dropfelt ⟨"%148"⟩;dropfelt ⟨"%152"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;dropfelt ⟨"%159"⟩⟧

-- Prove that substituting part29_state for Code.part29 produces the same result
lemma part29_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part29;dropfelt ⟨"%43"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%118"⟩;Code.part30;dropfelt ⟨"%46"⟩;dropfelt ⟨"%117"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%122"⟩;Code.part31;dropfelt ⟨"%49"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%123"⟩;dropfelt ⟨"%126"⟩;Code.part32;dropfelt ⟨"%52"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%130"⟩;Code.part33;dropfelt ⟨"%55"⟩;dropfelt ⟨"%129"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%134"⟩;Code.part34;dropfelt ⟨"%58"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%135"⟩;dropfelt ⟨"%138"⟩;Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%19"⟩;dropfelt ⟨"%73"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%108"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%120"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%132"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%140"⟩;dropfelt ⟨"%144"⟩;dropfelt ⟨"%148"⟩;dropfelt ⟨"%152"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;dropfelt ⟨"%159"⟩) st) ↔
  Code.getReturn (part29_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%43"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%118"⟩;Code.part30;dropfelt ⟨"%46"⟩;dropfelt ⟨"%117"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%122"⟩;Code.part31;dropfelt ⟨"%49"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%123"⟩;dropfelt ⟨"%126"⟩;Code.part32;dropfelt ⟨"%52"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%130"⟩;Code.part33;dropfelt ⟨"%55"⟩;dropfelt ⟨"%129"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%134"⟩;Code.part34;dropfelt ⟨"%58"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%135"⟩;dropfelt ⟨"%138"⟩;Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%19"⟩;dropfelt ⟨"%73"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%108"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%120"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%132"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%140"⟩;dropfelt ⟨"%144"⟩;dropfelt ⟨"%148"⟩;dropfelt ⟨"%152"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;dropfelt ⟨"%159"⟩) = prog
  unfold Code.part29
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part29_state_update part29_drops part29_state
  rfl

lemma part29_updates_opaque {st : State} : 
  Code.getReturn (part28_state_update st) ↔
  Code.getReturn (part29_state_update (part28_drops (part28_state st))) := by
  simp [part28_state_update, part29_wp]

lemma part29_cumulative_wp {x0 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19: Felt} :
  Code.run (start_state [x0] ([y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19])) ↔
  Code.getReturn
      (part29_state_update
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
                                                          True)[felts][{ name := "%43" }] ←
                                                        y9)[felts][{ name := "%46" }] ←
                                                      y10)[felts][{ name := "%49" }] ←
                                                    y11)[felts][{ name := "%52" }] ←
                                                  y12)[felts][{ name := "%55" }] ←
                                                y13)[felts][{ name := "%58" }] ←
                                              y14)[felts][{ name := "%61" }] ←
                                            y15)[felts][{ name := "%64" }] ←
                                          y16)[felts][{ name := "%67" }] ←
                                        y17)[felts][{ name := "%70" }] ←
                                      y18)[felts][{ name := "%73" }] ←
                                    y19)[props][{ name := "%77" }] ←
                                  y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 +
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
                              (y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 + y10 * 10 +
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
                            ((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 + y10 * 10 +
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
                          (((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 + y10 * 10 +
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
                        ((((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 + y10 * 10 +
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
                      (((((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 + y10 * 10 +
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
                    ((((((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 + y10 * 10 +
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
                  (((((((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 + y10 * 10 +
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
                ((((((((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 + y10 * 10 +
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
              (((((((((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 + y10 * 10 +
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
                (y8 = 0 ∨ 1 - y8 = 0)))[felts][{ name := "%113" }] ←
            y0 + y1 + y2 + y3 + y4 + y5 + y6 + y7 + y8)[felts][{ name := "%115" }] ←
          y9 * (1 - y9)))  := by
    rewrite [part28_cumulative_wp]
    rewrite [part29_updates_opaque]
    unfold part28_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part28_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

end Risc0.OneHot20.Constraints.WP