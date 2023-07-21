import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart34

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part35 on st
def part35_state (st: State) : State :=
  
        ((((st[props][{ name := "%140" : PropVar }] ←
                (Option.get! (State.props st { name := "%136" : PropVar }) ∧
                  Option.get! (State.felts st { name := "%139" : FeltVar }) =
                    (0 : Felt)))[felts][{ name := "%141" : FeltVar }] ←
              Option.get! (State.felts st { name := "%137" : FeltVar }) +
                Option.get! (State.felts st { name := "%61" : FeltVar }))[felts][{ name := "%142" : FeltVar }] ←
            Option.get! (State.felts st { name := "%0" : FeltVar }) -
              Option.get! (State.felts st { name := "%64" : FeltVar }))[felts][{ name := "%143" : FeltVar }] ←
          Option.get! (State.felts st { name := "%64" : FeltVar }) *
            (Option.get! (State.felts st { name := "%0" : FeltVar }) -
              Option.get! (State.felts st { name := "%64" : FeltVar }))) 

def part35_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%61"⟩) ⟨"%137"⟩) ⟨"%139"⟩) ⟨"%142"⟩

-- Run the program from part35 onwards by using part35_state rather than Code.part35
def part35_state_update (st: State): State :=
  Γ (part35_drops (part35_state st)) ⟦Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%73"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩⟧

-- Prove that substituting part35_state for Code.part35 produces the same result
lemma part35_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%73"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩) st) ↔
  Code.getReturn (part35_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%73"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩) = prog
  unfold Code.part35
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part35_state_update part35_drops part35_state
  rfl

lemma part35_updates_opaque {st : State} : 
  Code.getReturn (part34_state_update st) ↔
  Code.getReturn (part35_state_update (part34_drops (part34_state st))) := by
  simp [part34_state_update, part35_wp]

lemma part35_cumulative_wp {x0 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19: Felt} :
  Code.run (start_state [x0] ([y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19])) ↔
  Code.getReturn
      (part35_state_update
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
                                                          True)[felts][{ name := "%61" : FeltVar }] ←
                                                        y15)[felts][{ name := "%64" : FeltVar }] ←
                                                      y16)[felts][{ name := "%67" : FeltVar }] ←
                                                    y17)[felts][{ name := "%70" : FeltVar }] ←
                                                  y18)[felts][{ name := "%73" : FeltVar }] ←
                                                y19)[props][{ name := "%77" : PropVar }] ←
                                              y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) +
                                                                                y5 * (5 : Felt) +
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
                                            (y0 = (0 : Felt) ∨
                                              (1 : Felt) - y0 = (0 : Felt))))[props][{ name := "%84" : PropVar }] ←
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
                                          (y1 = (0 : Felt) ∨
                                            (1 : Felt) - y1 = (0 : Felt))))[props][{ name := "%88" : PropVar }] ←
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
                                        (y2 = (0 : Felt) ∨
                                          (1 : Felt) - y2 = (0 : Felt))))[props][{ name := "%92" : PropVar }] ←
                                    ((((y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) +
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
                                        (y2 = (0 : Felt) ∨ (1 : Felt) - y2 = (0 : Felt))) ∧
                                      (y3 = (0 : Felt) ∨
                                        (1 : Felt) - y3 = (0 : Felt))))[props][{ name := "%96" : PropVar }] ←
                                  (((((y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) +
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
                                        (y2 = (0 : Felt) ∨ (1 : Felt) - y2 = (0 : Felt))) ∧
                                      (y3 = (0 : Felt) ∨ (1 : Felt) - y3 = (0 : Felt))) ∧
                                    (y4 = (0 : Felt) ∨
                                      (1 : Felt) - y4 = (0 : Felt))))[props][{ name := "%100" : PropVar }] ←
                                ((((((y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) +
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
                                        (y2 = (0 : Felt) ∨ (1 : Felt) - y2 = (0 : Felt))) ∧
                                      (y3 = (0 : Felt) ∨ (1 : Felt) - y3 = (0 : Felt))) ∧
                                    (y4 = (0 : Felt) ∨ (1 : Felt) - y4 = (0 : Felt))) ∧
                                  (y5 = (0 : Felt) ∨
                                    (1 : Felt) - y5 = (0 : Felt))))[props][{ name := "%104" : PropVar }] ←
                              (((((((y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) +
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
                                        (y2 = (0 : Felt) ∨ (1 : Felt) - y2 = (0 : Felt))) ∧
                                      (y3 = (0 : Felt) ∨ (1 : Felt) - y3 = (0 : Felt))) ∧
                                    (y4 = (0 : Felt) ∨ (1 : Felt) - y4 = (0 : Felt))) ∧
                                  (y5 = (0 : Felt) ∨ (1 : Felt) - y5 = (0 : Felt))) ∧
                                (y6 = (0 : Felt) ∨
                                  (1 : Felt) - y6 = (0 : Felt))))[props][{ name := "%108" : PropVar }] ←
                            ((((((((y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) +
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
                                        (y2 = (0 : Felt) ∨ (1 : Felt) - y2 = (0 : Felt))) ∧
                                      (y3 = (0 : Felt) ∨ (1 : Felt) - y3 = (0 : Felt))) ∧
                                    (y4 = (0 : Felt) ∨ (1 : Felt) - y4 = (0 : Felt))) ∧
                                  (y5 = (0 : Felt) ∨ (1 : Felt) - y5 = (0 : Felt))) ∧
                                (y6 = (0 : Felt) ∨ (1 : Felt) - y6 = (0 : Felt))) ∧
                              (y7 = (0 : Felt) ∨ (1 : Felt) - y7 = (0 : Felt))))[props][{ name := "%112" : PropVar }] ←
                          (((((((((y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) +
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
                                        (y2 = (0 : Felt) ∨ (1 : Felt) - y2 = (0 : Felt))) ∧
                                      (y3 = (0 : Felt) ∨ (1 : Felt) - y3 = (0 : Felt))) ∧
                                    (y4 = (0 : Felt) ∨ (1 : Felt) - y4 = (0 : Felt))) ∧
                                  (y5 = (0 : Felt) ∨ (1 : Felt) - y5 = (0 : Felt))) ∧
                                (y6 = (0 : Felt) ∨ (1 : Felt) - y6 = (0 : Felt))) ∧
                              (y7 = (0 : Felt) ∨ (1 : Felt) - y7 = (0 : Felt))) ∧
                            (y8 = (0 : Felt) ∨ (1 : Felt) - y8 = (0 : Felt))))[props][{ name := "%116" : PropVar }] ←
                        ((((((((((y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) +
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
                                        (y2 = (0 : Felt) ∨ (1 : Felt) - y2 = (0 : Felt))) ∧
                                      (y3 = (0 : Felt) ∨ (1 : Felt) - y3 = (0 : Felt))) ∧
                                    (y4 = (0 : Felt) ∨ (1 : Felt) - y4 = (0 : Felt))) ∧
                                  (y5 = (0 : Felt) ∨ (1 : Felt) - y5 = (0 : Felt))) ∧
                                (y6 = (0 : Felt) ∨ (1 : Felt) - y6 = (0 : Felt))) ∧
                              (y7 = (0 : Felt) ∨ (1 : Felt) - y7 = (0 : Felt))) ∧
                            (y8 = (0 : Felt) ∨ (1 : Felt) - y8 = (0 : Felt))) ∧
                          (y9 = (0 : Felt) ∨ (1 : Felt) - y9 = (0 : Felt))))[props][{ name := "%120" : PropVar }] ←
                      (((((((((((y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) +
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
                                        (y2 = (0 : Felt) ∨ (1 : Felt) - y2 = (0 : Felt))) ∧
                                      (y3 = (0 : Felt) ∨ (1 : Felt) - y3 = (0 : Felt))) ∧
                                    (y4 = (0 : Felt) ∨ (1 : Felt) - y4 = (0 : Felt))) ∧
                                  (y5 = (0 : Felt) ∨ (1 : Felt) - y5 = (0 : Felt))) ∧
                                (y6 = (0 : Felt) ∨ (1 : Felt) - y6 = (0 : Felt))) ∧
                              (y7 = (0 : Felt) ∨ (1 : Felt) - y7 = (0 : Felt))) ∧
                            (y8 = (0 : Felt) ∨ (1 : Felt) - y8 = (0 : Felt))) ∧
                          (y9 = (0 : Felt) ∨ (1 : Felt) - y9 = (0 : Felt))) ∧
                        (y10 = (0 : Felt) ∨ (1 : Felt) - y10 = (0 : Felt))))[props][{ name := "%124" : PropVar }] ←
                    ((((((((((((y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) +
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
                                        (y2 = (0 : Felt) ∨ (1 : Felt) - y2 = (0 : Felt))) ∧
                                      (y3 = (0 : Felt) ∨ (1 : Felt) - y3 = (0 : Felt))) ∧
                                    (y4 = (0 : Felt) ∨ (1 : Felt) - y4 = (0 : Felt))) ∧
                                  (y5 = (0 : Felt) ∨ (1 : Felt) - y5 = (0 : Felt))) ∧
                                (y6 = (0 : Felt) ∨ (1 : Felt) - y6 = (0 : Felt))) ∧
                              (y7 = (0 : Felt) ∨ (1 : Felt) - y7 = (0 : Felt))) ∧
                            (y8 = (0 : Felt) ∨ (1 : Felt) - y8 = (0 : Felt))) ∧
                          (y9 = (0 : Felt) ∨ (1 : Felt) - y9 = (0 : Felt))) ∧
                        (y10 = (0 : Felt) ∨ (1 : Felt) - y10 = (0 : Felt))) ∧
                      (y11 = (0 : Felt) ∨ (1 : Felt) - y11 = (0 : Felt))))[props][{ name := "%128" : PropVar }] ←
                  (((((((((((((y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) +
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
                                        (y2 = (0 : Felt) ∨ (1 : Felt) - y2 = (0 : Felt))) ∧
                                      (y3 = (0 : Felt) ∨ (1 : Felt) - y3 = (0 : Felt))) ∧
                                    (y4 = (0 : Felt) ∨ (1 : Felt) - y4 = (0 : Felt))) ∧
                                  (y5 = (0 : Felt) ∨ (1 : Felt) - y5 = (0 : Felt))) ∧
                                (y6 = (0 : Felt) ∨ (1 : Felt) - y6 = (0 : Felt))) ∧
                              (y7 = (0 : Felt) ∨ (1 : Felt) - y7 = (0 : Felt))) ∧
                            (y8 = (0 : Felt) ∨ (1 : Felt) - y8 = (0 : Felt))) ∧
                          (y9 = (0 : Felt) ∨ (1 : Felt) - y9 = (0 : Felt))) ∧
                        (y10 = (0 : Felt) ∨ (1 : Felt) - y10 = (0 : Felt))) ∧
                      (y11 = (0 : Felt) ∨ (1 : Felt) - y11 = (0 : Felt))) ∧
                    (y12 = (0 : Felt) ∨ (1 : Felt) - y12 = (0 : Felt))))[props][{ name := "%132" : PropVar }] ←
                ((((((((((((((y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) +
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
                                        (y2 = (0 : Felt) ∨ (1 : Felt) - y2 = (0 : Felt))) ∧
                                      (y3 = (0 : Felt) ∨ (1 : Felt) - y3 = (0 : Felt))) ∧
                                    (y4 = (0 : Felt) ∨ (1 : Felt) - y4 = (0 : Felt))) ∧
                                  (y5 = (0 : Felt) ∨ (1 : Felt) - y5 = (0 : Felt))) ∧
                                (y6 = (0 : Felt) ∨ (1 : Felt) - y6 = (0 : Felt))) ∧
                              (y7 = (0 : Felt) ∨ (1 : Felt) - y7 = (0 : Felt))) ∧
                            (y8 = (0 : Felt) ∨ (1 : Felt) - y8 = (0 : Felt))) ∧
                          (y9 = (0 : Felt) ∨ (1 : Felt) - y9 = (0 : Felt))) ∧
                        (y10 = (0 : Felt) ∨ (1 : Felt) - y10 = (0 : Felt))) ∧
                      (y11 = (0 : Felt) ∨ (1 : Felt) - y11 = (0 : Felt))) ∧
                    (y12 = (0 : Felt) ∨ (1 : Felt) - y12 = (0 : Felt))) ∧
                  (y13 = (0 : Felt) ∨ (1 : Felt) - y13 = (0 : Felt))))[props][{ name := "%136" : PropVar }] ←
              (((((((((((((((y1 + y2 * (2 : Felt) + y3 * (3 : Felt) + y4 * (4 : Felt) + y5 * (5 : Felt) +
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
                                        (y2 = (0 : Felt) ∨ (1 : Felt) - y2 = (0 : Felt))) ∧
                                      (y3 = (0 : Felt) ∨ (1 : Felt) - y3 = (0 : Felt))) ∧
                                    (y4 = (0 : Felt) ∨ (1 : Felt) - y4 = (0 : Felt))) ∧
                                  (y5 = (0 : Felt) ∨ (1 : Felt) - y5 = (0 : Felt))) ∧
                                (y6 = (0 : Felt) ∨ (1 : Felt) - y6 = (0 : Felt))) ∧
                              (y7 = (0 : Felt) ∨ (1 : Felt) - y7 = (0 : Felt))) ∧
                            (y8 = (0 : Felt) ∨ (1 : Felt) - y8 = (0 : Felt))) ∧
                          (y9 = (0 : Felt) ∨ (1 : Felt) - y9 = (0 : Felt))) ∧
                        (y10 = (0 : Felt) ∨ (1 : Felt) - y10 = (0 : Felt))) ∧
                      (y11 = (0 : Felt) ∨ (1 : Felt) - y11 = (0 : Felt))) ∧
                    (y12 = (0 : Felt) ∨ (1 : Felt) - y12 = (0 : Felt))) ∧
                  (y13 = (0 : Felt) ∨ (1 : Felt) - y13 = (0 : Felt))) ∧
                (y14 = (0 : Felt) ∨ (1 : Felt) - y14 = (0 : Felt))))[felts][{ name := "%137" : FeltVar }] ←
            y0 + y1 + y2 + y3 + y4 + y5 + y6 + y7 + y8 + y9 + y10 + y11 + y12 + y13 +
              y14)[felts][{ name := "%139" : FeltVar }] ←
          y15 * ((1 : Felt) - y15)))  := by
    rewrite [part34_cumulative_wp]
    rewrite [part35_updates_opaque]
    unfold part34_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part34_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.constraints_if_eq_if_constraints,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.OneHot20.Constraints.WP