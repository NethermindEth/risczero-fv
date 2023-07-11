import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart27

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part28 on st
def part28_state (st: State) : State :=
  
        ((((st[props][{ name := "%112" : PropVar }] ←
                (Option.get! (State.props st { name := "%108" : PropVar }) ∧
                  Option.get! (State.felts st { name := "%111" : FeltVar }) =
                    (0 : Felt)))[felts][{ name := "%113" : FeltVar }] ←
              Option.get! (State.felts st { name := "%109" : FeltVar }) +
                Option.get! (State.felts st { name := "%40" : FeltVar }))[felts][{ name := "%114" : FeltVar }] ←
            Option.get! (State.felts st { name := "%0" : FeltVar }) -
              Option.get! (State.felts st { name := "%43" : FeltVar }))[felts][{ name := "%115" : FeltVar }] ←
          Option.get! (State.felts st { name := "%43" : FeltVar }) *
            (Option.get! (State.felts st { name := "%0" : FeltVar }) -
              Option.get! (State.felts st { name := "%43" : FeltVar }))) 

def part28_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%40"⟩) ⟨"%109"⟩) ⟨"%111"⟩) ⟨"%114"⟩

-- Run the program from part28 onwards by using part28_state rather than Code.part28
def part28_state_update (st: State): State :=
  Γ (part28_drops (part28_state st)) ⟦Code.part29;dropfelt ⟨"%43"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%118"⟩;Code.part30;dropfelt ⟨"%46"⟩;dropfelt ⟨"%117"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%122"⟩;Code.part31;dropfelt ⟨"%49"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%123"⟩;dropfelt ⟨"%126"⟩;Code.part32;dropfelt ⟨"%52"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%130"⟩;Code.part33;dropfelt ⟨"%55"⟩;dropfelt ⟨"%129"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%134"⟩;Code.part34;dropfelt ⟨"%58"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%135"⟩;dropfelt ⟨"%138"⟩;Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%19"⟩;dropfelt ⟨"%73"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%108"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%120"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%132"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%140"⟩;dropfelt ⟨"%144"⟩;dropfelt ⟨"%148"⟩;dropfelt ⟨"%152"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;dropfelt ⟨"%159"⟩⟧

-- Prove that substituting part28_state for Code.part28 produces the same result
lemma part28_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part28;dropfelt ⟨"%40"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%111"⟩;dropfelt ⟨"%114"⟩;Code.part29;dropfelt ⟨"%43"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%118"⟩;Code.part30;dropfelt ⟨"%46"⟩;dropfelt ⟨"%117"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%122"⟩;Code.part31;dropfelt ⟨"%49"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%123"⟩;dropfelt ⟨"%126"⟩;Code.part32;dropfelt ⟨"%52"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%130"⟩;Code.part33;dropfelt ⟨"%55"⟩;dropfelt ⟨"%129"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%134"⟩;Code.part34;dropfelt ⟨"%58"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%135"⟩;dropfelt ⟨"%138"⟩;Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%19"⟩;dropfelt ⟨"%73"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%108"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%120"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%132"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%140"⟩;dropfelt ⟨"%144"⟩;dropfelt ⟨"%148"⟩;dropfelt ⟨"%152"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;dropfelt ⟨"%159"⟩) st) ↔
  Code.getReturn (part28_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%40"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%111"⟩;dropfelt ⟨"%114"⟩;Code.part29;dropfelt ⟨"%43"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%118"⟩;Code.part30;dropfelt ⟨"%46"⟩;dropfelt ⟨"%117"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%122"⟩;Code.part31;dropfelt ⟨"%49"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%123"⟩;dropfelt ⟨"%126"⟩;Code.part32;dropfelt ⟨"%52"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%130"⟩;Code.part33;dropfelt ⟨"%55"⟩;dropfelt ⟨"%129"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%134"⟩;Code.part34;dropfelt ⟨"%58"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%135"⟩;dropfelt ⟨"%138"⟩;Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%19"⟩;dropfelt ⟨"%73"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%108"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%120"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%132"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%140"⟩;dropfelt ⟨"%144"⟩;dropfelt ⟨"%148"⟩;dropfelt ⟨"%152"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;dropfelt ⟨"%159"⟩) = prog
  unfold Code.part28
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part28_state_update part28_drops part28_state
  rfl

lemma part28_updates_opaque {st : State} : 
  Code.getReturn (part27_state_update st) ↔
  Code.getReturn (part28_state_update (part27_drops (part27_state st))) := by
  simp [part27_state_update, part28_wp]

lemma part28_cumulative_wp {x0 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19: Felt} :
  Code.run (start_state [x0] ([y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19])) ↔
  Code.getReturn
      (part28_state_update
        ((((((((((((((((((((((((({
                                                            buffers :=
                                                              ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                                                  [[some y0, some y1, some y2, some y3, some y4,
                                                                      some y5, some y6, some y7, some y8, some y9,
                                                                      some y10, some y11, some y12, some y13, some y14,
                                                                      some y15, some y16, some y17, some y18,
                                                                      some y19]])[{ name := "code" : BufferVar }] ←ₘ
                                                                [[some x0]],
                                                            bufferWidths :=
                                                              ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                                                  (20 : ℕ))[{ name := "code" : BufferVar }] ←ₘ
                                                                (1 : ℕ),
                                                            constraints := [], cycle := (0 : ℕ), felts := Map.empty,
                                                            isFailed := false, props := Map.empty,
                                                            vars :=
                                                              [{ name := "code" : BufferVar },
                                                                { name := "data" :
                                                                  BufferVar }] }[props][{ name := "%19" : PropVar }] ←
                                                          True)[felts][{ name := "%40" : FeltVar }] ←
                                                        y8)[felts][{ name := "%43" : FeltVar }] ←
                                                      y9)[felts][{ name := "%46" : FeltVar }] ←
                                                    y10)[felts][{ name := "%49" : FeltVar }] ←
                                                  y11)[felts][{ name := "%52" : FeltVar }] ←
                                                y12)[felts][{ name := "%55" : FeltVar }] ←
                                              y13)[felts][{ name := "%58" : FeltVar }] ←
                                            y14)[felts][{ name := "%61" : FeltVar }] ←
                                          y15)[felts][{ name := "%64" : FeltVar }] ←
                                        y16)[felts][{ name := "%67" : FeltVar }] ←
                                      y17)[felts][{ name := "%70" : FeltVar }] ←
                                    y18)[felts][{ name := "%73" : FeltVar }] ←
                                  y19)[props][{ name := "%77" : PropVar }] ←
                                y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) +
                                                                y6 * (6 : Felt) +
                                                              y7 * (7 : Felt) +
                                                            y8 * (8 : Felt) +
                                                          y9 * (9 : Felt) +
                                                        y10 * (10 : Felt) +
                                                      y11 * (11 : Felt) +
                                                    y12 * (12 : Felt) +
                                                  y13 * (13 : Felt) +
                                                y14 * (14 : Felt) +
                                              y15 * (15 : Felt) +
                                            y16 * (16 : Felt) +
                                          y17 * (17 : Felt) +
                                        y18 * (18 : Felt) +
                                      y19 * (19 : Felt) -
                                    x0 =
                                  (0 : Felt))[felts][{ name := "%0" : FeltVar }] ←
                              (1 : Felt))[props][{ name := "%81" : PropVar }] ←
                            (y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) +
                                                              y6 * (6 : Felt) +
                                                            y7 * (7 : Felt) +
                                                          y8 * (8 : Felt) +
                                                        y9 * (9 : Felt) +
                                                      y10 * (10 : Felt) +
                                                    y11 * (11 : Felt) +
                                                  y12 * (12 : Felt) +
                                                y13 * (13 : Felt) +
                                              y14 * (14 : Felt) +
                                            y15 * (15 : Felt) +
                                          y16 * (16 : Felt) +
                                        y17 * (17 : Felt) +
                                      y18 * (18 : Felt) +
                                    y19 * (19 : Felt) -
                                  x0 =
                                (0 : Felt) ∧
                              (y0 = (0 : Felt) ∨ (1 : Felt) - y0 = (0 : Felt))))[props][{ name := "%84" : PropVar }] ←
                          ((y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) +
                                                              y6 * (6 : Felt) +
                                                            y7 * (7 : Felt) +
                                                          y8 * (8 : Felt) +
                                                        y9 * (9 : Felt) +
                                                      y10 * (10 : Felt) +
                                                    y11 * (11 : Felt) +
                                                  y12 * (12 : Felt) +
                                                y13 * (13 : Felt) +
                                              y14 * (14 : Felt) +
                                            y15 * (15 : Felt) +
                                          y16 * (16 : Felt) +
                                        y17 * (17 : Felt) +
                                      y18 * (18 : Felt) +
                                    y19 * (19 : Felt) -
                                  x0 =
                                (0 : Felt) ∧
                              (y0 = (0 : Felt) ∨ (1 : Felt) - y0 = (0 : Felt))) ∧
                            (y1 = (0 : Felt) ∨ (1 : Felt) - y1 = (0 : Felt))))[props][{ name := "%88" : PropVar }] ←
                        (((y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) +
                                                              y6 * (6 : Felt) +
                                                            y7 * (7 : Felt) +
                                                          y8 * (8 : Felt) +
                                                        y9 * (9 : Felt) +
                                                      y10 * (10 : Felt) +
                                                    y11 * (11 : Felt) +
                                                  y12 * (12 : Felt) +
                                                y13 * (13 : Felt) +
                                              y14 * (14 : Felt) +
                                            y15 * (15 : Felt) +
                                          y16 * (16 : Felt) +
                                        y17 * (17 : Felt) +
                                      y18 * (18 : Felt) +
                                    y19 * (19 : Felt) -
                                  x0 =
                                (0 : Felt) ∧
                              (y0 = (0 : Felt) ∨ (1 : Felt) - y0 = (0 : Felt))) ∧
                            (y1 = (0 : Felt) ∨ (1 : Felt) - y1 = (0 : Felt))) ∧
                          (y2 = (0 : Felt) ∨ (1 : Felt) - y2 = (0 : Felt))))[props][{ name := "%92" : PropVar }] ←
                      ((((y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) + y6 * (6 : Felt) +
                                                            y7 * (7 : Felt) +
                                                          y8 * (8 : Felt) +
                                                        y9 * (9 : Felt) +
                                                      y10 * (10 : Felt) +
                                                    y11 * (11 : Felt) +
                                                  y12 * (12 : Felt) +
                                                y13 * (13 : Felt) +
                                              y14 * (14 : Felt) +
                                            y15 * (15 : Felt) +
                                          y16 * (16 : Felt) +
                                        y17 * (17 : Felt) +
                                      y18 * (18 : Felt) +
                                    y19 * (19 : Felt) -
                                  x0 =
                                (0 : Felt) ∧
                              (y0 = (0 : Felt) ∨ (1 : Felt) - y0 = (0 : Felt))) ∧
                            (y1 = (0 : Felt) ∨ (1 : Felt) - y1 = (0 : Felt))) ∧
                          (y2 = (0 : Felt) ∨ (1 : Felt) - y2 = (0 : Felt))) ∧
                        (y3 = (0 : Felt) ∨ (1 : Felt) - y3 = (0 : Felt))))[props][{ name := "%96" : PropVar }] ←
                    (((((y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) + y6 * (6 : Felt) +
                                                            y7 * (7 : Felt) +
                                                          y8 * (8 : Felt) +
                                                        y9 * (9 : Felt) +
                                                      y10 * (10 : Felt) +
                                                    y11 * (11 : Felt) +
                                                  y12 * (12 : Felt) +
                                                y13 * (13 : Felt) +
                                              y14 * (14 : Felt) +
                                            y15 * (15 : Felt) +
                                          y16 * (16 : Felt) +
                                        y17 * (17 : Felt) +
                                      y18 * (18 : Felt) +
                                    y19 * (19 : Felt) -
                                  x0 =
                                (0 : Felt) ∧
                              (y0 = (0 : Felt) ∨ (1 : Felt) - y0 = (0 : Felt))) ∧
                            (y1 = (0 : Felt) ∨ (1 : Felt) - y1 = (0 : Felt))) ∧
                          (y2 = (0 : Felt) ∨ (1 : Felt) - y2 = (0 : Felt))) ∧
                        (y3 = (0 : Felt) ∨ (1 : Felt) - y3 = (0 : Felt))) ∧
                      (y4 = (0 : Felt) ∨ (1 : Felt) - y4 = (0 : Felt))))[props][{ name := "%100" : PropVar }] ←
                  ((((((y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) + y6 * (6 : Felt) +
                                                            y7 * (7 : Felt) +
                                                          y8 * (8 : Felt) +
                                                        y9 * (9 : Felt) +
                                                      y10 * (10 : Felt) +
                                                    y11 * (11 : Felt) +
                                                  y12 * (12 : Felt) +
                                                y13 * (13 : Felt) +
                                              y14 * (14 : Felt) +
                                            y15 * (15 : Felt) +
                                          y16 * (16 : Felt) +
                                        y17 * (17 : Felt) +
                                      y18 * (18 : Felt) +
                                    y19 * (19 : Felt) -
                                  x0 =
                                (0 : Felt) ∧
                              (y0 = (0 : Felt) ∨ (1 : Felt) - y0 = (0 : Felt))) ∧
                            (y1 = (0 : Felt) ∨ (1 : Felt) - y1 = (0 : Felt))) ∧
                          (y2 = (0 : Felt) ∨ (1 : Felt) - y2 = (0 : Felt))) ∧
                        (y3 = (0 : Felt) ∨ (1 : Felt) - y3 = (0 : Felt))) ∧
                      (y4 = (0 : Felt) ∨ (1 : Felt) - y4 = (0 : Felt))) ∧
                    (y5 = (0 : Felt) ∨ (1 : Felt) - y5 = (0 : Felt))))[props][{ name := "%104" : PropVar }] ←
                (((((((y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) + y6 * (6 : Felt) +
                                                            y7 * (7 : Felt) +
                                                          y8 * (8 : Felt) +
                                                        y9 * (9 : Felt) +
                                                      y10 * (10 : Felt) +
                                                    y11 * (11 : Felt) +
                                                  y12 * (12 : Felt) +
                                                y13 * (13 : Felt) +
                                              y14 * (14 : Felt) +
                                            y15 * (15 : Felt) +
                                          y16 * (16 : Felt) +
                                        y17 * (17 : Felt) +
                                      y18 * (18 : Felt) +
                                    y19 * (19 : Felt) -
                                  x0 =
                                (0 : Felt) ∧
                              (y0 = (0 : Felt) ∨ (1 : Felt) - y0 = (0 : Felt))) ∧
                            (y1 = (0 : Felt) ∨ (1 : Felt) - y1 = (0 : Felt))) ∧
                          (y2 = (0 : Felt) ∨ (1 : Felt) - y2 = (0 : Felt))) ∧
                        (y3 = (0 : Felt) ∨ (1 : Felt) - y3 = (0 : Felt))) ∧
                      (y4 = (0 : Felt) ∨ (1 : Felt) - y4 = (0 : Felt))) ∧
                    (y5 = (0 : Felt) ∨ (1 : Felt) - y5 = (0 : Felt))) ∧
                  (y6 = (0 : Felt) ∨ (1 : Felt) - y6 = (0 : Felt))))[props][{ name := "%108" : PropVar }] ←
              ((((((((y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) + y6 * (6 : Felt) +
                                                            y7 * (7 : Felt) +
                                                          y8 * (8 : Felt) +
                                                        y9 * (9 : Felt) +
                                                      y10 * (10 : Felt) +
                                                    y11 * (11 : Felt) +
                                                  y12 * (12 : Felt) +
                                                y13 * (13 : Felt) +
                                              y14 * (14 : Felt) +
                                            y15 * (15 : Felt) +
                                          y16 * (16 : Felt) +
                                        y17 * (17 : Felt) +
                                      y18 * (18 : Felt) +
                                    y19 * (19 : Felt) -
                                  x0 =
                                (0 : Felt) ∧
                              (y0 = (0 : Felt) ∨ (1 : Felt) - y0 = (0 : Felt))) ∧
                            (y1 = (0 : Felt) ∨ (1 : Felt) - y1 = (0 : Felt))) ∧
                          (y2 = (0 : Felt) ∨ (1 : Felt) - y2 = (0 : Felt))) ∧
                        (y3 = (0 : Felt) ∨ (1 : Felt) - y3 = (0 : Felt))) ∧
                      (y4 = (0 : Felt) ∨ (1 : Felt) - y4 = (0 : Felt))) ∧
                    (y5 = (0 : Felt) ∨ (1 : Felt) - y5 = (0 : Felt))) ∧
                  (y6 = (0 : Felt) ∨ (1 : Felt) - y6 = (0 : Felt))) ∧
                (y7 = (0 : Felt) ∨ (1 : Felt) - y7 = (0 : Felt))))[felts][{ name := "%109" : FeltVar }] ←
            y0 + y1 + y2 + y3 + y4 + y5 + y6 + y7)[felts][{ name := "%111" : FeltVar }] ←
          y8 * ((1 : Felt) - y8)))  := by
    rewrite [part27_cumulative_wp]
    rewrite [part28_updates_opaque]
    unfold part27_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part27_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

end Risc0.OneHot20.Constraints.WP