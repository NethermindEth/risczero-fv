import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart33

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part34 on st
def part34_state (st: State) : State :=
  
        ((((st[props][{ name := "%136" : PropVar }] ←
                (Option.get! (State.props st { name := "%132" : PropVar }) ∧
                  Option.get! (State.felts st { name := "%135" : FeltVar }) =
                    (0 : Felt)))[felts][{ name := "%137" : FeltVar }] ←
              Option.get! (State.felts st { name := "%133" : FeltVar }) +
                Option.get! (State.felts st { name := "%58" : FeltVar }))[felts][{ name := "%138" : FeltVar }] ←
            Option.get! (State.felts st { name := "%0" : FeltVar }) -
              Option.get! (State.felts st { name := "%61" : FeltVar }))[felts][{ name := "%139" : FeltVar }] ←
          Option.get! (State.felts st { name := "%61" : FeltVar }) *
            (Option.get! (State.felts st { name := "%0" : FeltVar }) -
              Option.get! (State.felts st { name := "%61" : FeltVar }))) 

def part34_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%58"⟩) ⟨"%133"⟩) ⟨"%135"⟩) ⟨"%138"⟩

-- Run the program from part34 onwards by using part34_state rather than Code.part34
def part34_state_update (st: State): State :=
  Γ (part34_drops (part34_state st)) ⟦Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%73"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩⟧

-- Prove that substituting part34_state for Code.part34 produces the same result
lemma part34_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part34;dropfelt ⟨"%58"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%135"⟩;dropfelt ⟨"%138"⟩;Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%73"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩) st) ↔
  Code.getReturn (part34_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%58"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%135"⟩;dropfelt ⟨"%138"⟩;Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%73"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩) = prog
  unfold Code.part34
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part34_state_update part34_drops part34_state
  rfl

lemma part34_updates_opaque {st : State} : 
  Code.getReturn (part33_state_update st) ↔
  Code.getReturn (part34_state_update (part33_drops (part33_state st))) := by
  simp [part33_state_update, part34_wp]

lemma part34_cumulative_wp {code0 data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 data18 data19: Felt} :
  Code.run (start_state ([code0]) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19])) ↔
  Code.getReturn
      (part34_state_update
        ((((((((((((((((((((((((({
                                                            buffers :=
                                                              ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                                                  [[some data0, some data1, some data2, some data3,
                                                                      some data4, some data5, some data6, some data7,
                                                                      some data8, some data9, some data10, some data11,
                                                                      some data12, some data13, some data14,
                                                                      some data15, some data16, some data17,
                                                                      some data18,
                                                                      some data19]])[{ name := "code" : BufferVar }] ←ₘ
                                                                [[some code0]],
                                                            bufferWidths :=
                                                              ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                                                  (20 : ℕ))[{ name := "code" : BufferVar }] ←ₘ
                                                                (1 : ℕ),
                                                            cycle := (0 : ℕ), felts := Map.empty, isFailed := False,
                                                            props := Map.empty,
                                                            vars :=
                                                              [{ name := "code" : BufferVar },
                                                                { name := "data" :
                                                                  BufferVar }] }[props][{ name := "%19" : PropVar }] ←
                                                          True)[felts][{ name := "%58" : FeltVar }] ←
                                                        data14)[felts][{ name := "%61" : FeltVar }] ←
                                                      data15)[felts][{ name := "%64" : FeltVar }] ←
                                                    data16)[felts][{ name := "%67" : FeltVar }] ←
                                                  data17)[felts][{ name := "%70" : FeltVar }] ←
                                                data18)[felts][{ name := "%73" : FeltVar }] ←
                                              data19)[props][{ name := "%77" : PropVar }] ←
                                            data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) +
                                                                              data5 * (5 : Felt) +
                                                                            data6 * (6 : Felt) +
                                                                          data7 * (7 : Felt) +
                                                                        data8 * (8 : Felt) +
                                                                      data9 * (9 : Felt) +
                                                                    data10 * (10 : Felt) +
                                                                  data11 * (11 : Felt) +
                                                                data12 * (12 : Felt) +
                                                              data13 * (13 : Felt) +
                                                            data14 * (14 : Felt) +
                                                          data15 * (15 : Felt) +
                                                        data16 * (16 : Felt) +
                                                      data17 * (17 : Felt) +
                                                    data18 * (18 : Felt) +
                                                  data19 * (19 : Felt) -
                                                code0 =
                                              (0 : Felt))[felts][{ name := "%0" : FeltVar }] ←
                                          (1 : Felt))[props][{ name := "%81" : PropVar }] ←
                                        (data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) +
                                                                            data5 * (5 : Felt) +
                                                                          data6 * (6 : Felt) +
                                                                        data7 * (7 : Felt) +
                                                                      data8 * (8 : Felt) +
                                                                    data9 * (9 : Felt) +
                                                                  data10 * (10 : Felt) +
                                                                data11 * (11 : Felt) +
                                                              data12 * (12 : Felt) +
                                                            data13 * (13 : Felt) +
                                                          data14 * (14 : Felt) +
                                                        data15 * (15 : Felt) +
                                                      data16 * (16 : Felt) +
                                                    data17 * (17 : Felt) +
                                                  data18 * (18 : Felt) +
                                                data19 * (19 : Felt) -
                                              code0 =
                                            (0 : Felt) ∧
                                          (data0 = (0 : Felt) ∨
                                            (1 : Felt) - data0 = (0 : Felt))))[props][{ name := "%84" : PropVar }] ←
                                      ((data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) +
                                                                            data5 * (5 : Felt) +
                                                                          data6 * (6 : Felt) +
                                                                        data7 * (7 : Felt) +
                                                                      data8 * (8 : Felt) +
                                                                    data9 * (9 : Felt) +
                                                                  data10 * (10 : Felt) +
                                                                data11 * (11 : Felt) +
                                                              data12 * (12 : Felt) +
                                                            data13 * (13 : Felt) +
                                                          data14 * (14 : Felt) +
                                                        data15 * (15 : Felt) +
                                                      data16 * (16 : Felt) +
                                                    data17 * (17 : Felt) +
                                                  data18 * (18 : Felt) +
                                                data19 * (19 : Felt) -
                                              code0 =
                                            (0 : Felt) ∧
                                          (data0 = (0 : Felt) ∨ (1 : Felt) - data0 = (0 : Felt))) ∧
                                        (data1 = (0 : Felt) ∨
                                          (1 : Felt) - data1 = (0 : Felt))))[props][{ name := "%88" : PropVar }] ←
                                    (((data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) +
                                                                            data5 * (5 : Felt) +
                                                                          data6 * (6 : Felt) +
                                                                        data7 * (7 : Felt) +
                                                                      data8 * (8 : Felt) +
                                                                    data9 * (9 : Felt) +
                                                                  data10 * (10 : Felt) +
                                                                data11 * (11 : Felt) +
                                                              data12 * (12 : Felt) +
                                                            data13 * (13 : Felt) +
                                                          data14 * (14 : Felt) +
                                                        data15 * (15 : Felt) +
                                                      data16 * (16 : Felt) +
                                                    data17 * (17 : Felt) +
                                                  data18 * (18 : Felt) +
                                                data19 * (19 : Felt) -
                                              code0 =
                                            (0 : Felt) ∧
                                          (data0 = (0 : Felt) ∨ (1 : Felt) - data0 = (0 : Felt))) ∧
                                        (data1 = (0 : Felt) ∨ (1 : Felt) - data1 = (0 : Felt))) ∧
                                      (data2 = (0 : Felt) ∨
                                        (1 : Felt) - data2 = (0 : Felt))))[props][{ name := "%92" : PropVar }] ←
                                  ((((data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) +
                                                                            data5 * (5 : Felt) +
                                                                          data6 * (6 : Felt) +
                                                                        data7 * (7 : Felt) +
                                                                      data8 * (8 : Felt) +
                                                                    data9 * (9 : Felt) +
                                                                  data10 * (10 : Felt) +
                                                                data11 * (11 : Felt) +
                                                              data12 * (12 : Felt) +
                                                            data13 * (13 : Felt) +
                                                          data14 * (14 : Felt) +
                                                        data15 * (15 : Felt) +
                                                      data16 * (16 : Felt) +
                                                    data17 * (17 : Felt) +
                                                  data18 * (18 : Felt) +
                                                data19 * (19 : Felt) -
                                              code0 =
                                            (0 : Felt) ∧
                                          (data0 = (0 : Felt) ∨ (1 : Felt) - data0 = (0 : Felt))) ∧
                                        (data1 = (0 : Felt) ∨ (1 : Felt) - data1 = (0 : Felt))) ∧
                                      (data2 = (0 : Felt) ∨ (1 : Felt) - data2 = (0 : Felt))) ∧
                                    (data3 = (0 : Felt) ∨
                                      (1 : Felt) - data3 = (0 : Felt))))[props][{ name := "%96" : PropVar }] ←
                                (((((data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) +
                                                                            data5 * (5 : Felt) +
                                                                          data6 * (6 : Felt) +
                                                                        data7 * (7 : Felt) +
                                                                      data8 * (8 : Felt) +
                                                                    data9 * (9 : Felt) +
                                                                  data10 * (10 : Felt) +
                                                                data11 * (11 : Felt) +
                                                              data12 * (12 : Felt) +
                                                            data13 * (13 : Felt) +
                                                          data14 * (14 : Felt) +
                                                        data15 * (15 : Felt) +
                                                      data16 * (16 : Felt) +
                                                    data17 * (17 : Felt) +
                                                  data18 * (18 : Felt) +
                                                data19 * (19 : Felt) -
                                              code0 =
                                            (0 : Felt) ∧
                                          (data0 = (0 : Felt) ∨ (1 : Felt) - data0 = (0 : Felt))) ∧
                                        (data1 = (0 : Felt) ∨ (1 : Felt) - data1 = (0 : Felt))) ∧
                                      (data2 = (0 : Felt) ∨ (1 : Felt) - data2 = (0 : Felt))) ∧
                                    (data3 = (0 : Felt) ∨ (1 : Felt) - data3 = (0 : Felt))) ∧
                                  (data4 = (0 : Felt) ∨
                                    (1 : Felt) - data4 = (0 : Felt))))[props][{ name := "%100" : PropVar }] ←
                              ((((((data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) +
                                                                            data5 * (5 : Felt) +
                                                                          data6 * (6 : Felt) +
                                                                        data7 * (7 : Felt) +
                                                                      data8 * (8 : Felt) +
                                                                    data9 * (9 : Felt) +
                                                                  data10 * (10 : Felt) +
                                                                data11 * (11 : Felt) +
                                                              data12 * (12 : Felt) +
                                                            data13 * (13 : Felt) +
                                                          data14 * (14 : Felt) +
                                                        data15 * (15 : Felt) +
                                                      data16 * (16 : Felt) +
                                                    data17 * (17 : Felt) +
                                                  data18 * (18 : Felt) +
                                                data19 * (19 : Felt) -
                                              code0 =
                                            (0 : Felt) ∧
                                          (data0 = (0 : Felt) ∨ (1 : Felt) - data0 = (0 : Felt))) ∧
                                        (data1 = (0 : Felt) ∨ (1 : Felt) - data1 = (0 : Felt))) ∧
                                      (data2 = (0 : Felt) ∨ (1 : Felt) - data2 = (0 : Felt))) ∧
                                    (data3 = (0 : Felt) ∨ (1 : Felt) - data3 = (0 : Felt))) ∧
                                  (data4 = (0 : Felt) ∨ (1 : Felt) - data4 = (0 : Felt))) ∧
                                (data5 = (0 : Felt) ∨
                                  (1 : Felt) - data5 = (0 : Felt))))[props][{ name := "%104" : PropVar }] ←
                            (((((((data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) +
                                                                            data5 * (5 : Felt) +
                                                                          data6 * (6 : Felt) +
                                                                        data7 * (7 : Felt) +
                                                                      data8 * (8 : Felt) +
                                                                    data9 * (9 : Felt) +
                                                                  data10 * (10 : Felt) +
                                                                data11 * (11 : Felt) +
                                                              data12 * (12 : Felt) +
                                                            data13 * (13 : Felt) +
                                                          data14 * (14 : Felt) +
                                                        data15 * (15 : Felt) +
                                                      data16 * (16 : Felt) +
                                                    data17 * (17 : Felt) +
                                                  data18 * (18 : Felt) +
                                                data19 * (19 : Felt) -
                                              code0 =
                                            (0 : Felt) ∧
                                          (data0 = (0 : Felt) ∨ (1 : Felt) - data0 = (0 : Felt))) ∧
                                        (data1 = (0 : Felt) ∨ (1 : Felt) - data1 = (0 : Felt))) ∧
                                      (data2 = (0 : Felt) ∨ (1 : Felt) - data2 = (0 : Felt))) ∧
                                    (data3 = (0 : Felt) ∨ (1 : Felt) - data3 = (0 : Felt))) ∧
                                  (data4 = (0 : Felt) ∨ (1 : Felt) - data4 = (0 : Felt))) ∧
                                (data5 = (0 : Felt) ∨ (1 : Felt) - data5 = (0 : Felt))) ∧
                              (data6 = (0 : Felt) ∨
                                (1 : Felt) - data6 = (0 : Felt))))[props][{ name := "%108" : PropVar }] ←
                          ((((((((data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) +
                                                                            data5 * (5 : Felt) +
                                                                          data6 * (6 : Felt) +
                                                                        data7 * (7 : Felt) +
                                                                      data8 * (8 : Felt) +
                                                                    data9 * (9 : Felt) +
                                                                  data10 * (10 : Felt) +
                                                                data11 * (11 : Felt) +
                                                              data12 * (12 : Felt) +
                                                            data13 * (13 : Felt) +
                                                          data14 * (14 : Felt) +
                                                        data15 * (15 : Felt) +
                                                      data16 * (16 : Felt) +
                                                    data17 * (17 : Felt) +
                                                  data18 * (18 : Felt) +
                                                data19 * (19 : Felt) -
                                              code0 =
                                            (0 : Felt) ∧
                                          (data0 = (0 : Felt) ∨ (1 : Felt) - data0 = (0 : Felt))) ∧
                                        (data1 = (0 : Felt) ∨ (1 : Felt) - data1 = (0 : Felt))) ∧
                                      (data2 = (0 : Felt) ∨ (1 : Felt) - data2 = (0 : Felt))) ∧
                                    (data3 = (0 : Felt) ∨ (1 : Felt) - data3 = (0 : Felt))) ∧
                                  (data4 = (0 : Felt) ∨ (1 : Felt) - data4 = (0 : Felt))) ∧
                                (data5 = (0 : Felt) ∨ (1 : Felt) - data5 = (0 : Felt))) ∧
                              (data6 = (0 : Felt) ∨ (1 : Felt) - data6 = (0 : Felt))) ∧
                            (data7 = (0 : Felt) ∨
                              (1 : Felt) - data7 = (0 : Felt))))[props][{ name := "%112" : PropVar }] ←
                        (((((((((data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) +
                                                                            data5 * (5 : Felt) +
                                                                          data6 * (6 : Felt) +
                                                                        data7 * (7 : Felt) +
                                                                      data8 * (8 : Felt) +
                                                                    data9 * (9 : Felt) +
                                                                  data10 * (10 : Felt) +
                                                                data11 * (11 : Felt) +
                                                              data12 * (12 : Felt) +
                                                            data13 * (13 : Felt) +
                                                          data14 * (14 : Felt) +
                                                        data15 * (15 : Felt) +
                                                      data16 * (16 : Felt) +
                                                    data17 * (17 : Felt) +
                                                  data18 * (18 : Felt) +
                                                data19 * (19 : Felt) -
                                              code0 =
                                            (0 : Felt) ∧
                                          (data0 = (0 : Felt) ∨ (1 : Felt) - data0 = (0 : Felt))) ∧
                                        (data1 = (0 : Felt) ∨ (1 : Felt) - data1 = (0 : Felt))) ∧
                                      (data2 = (0 : Felt) ∨ (1 : Felt) - data2 = (0 : Felt))) ∧
                                    (data3 = (0 : Felt) ∨ (1 : Felt) - data3 = (0 : Felt))) ∧
                                  (data4 = (0 : Felt) ∨ (1 : Felt) - data4 = (0 : Felt))) ∧
                                (data5 = (0 : Felt) ∨ (1 : Felt) - data5 = (0 : Felt))) ∧
                              (data6 = (0 : Felt) ∨ (1 : Felt) - data6 = (0 : Felt))) ∧
                            (data7 = (0 : Felt) ∨ (1 : Felt) - data7 = (0 : Felt))) ∧
                          (data8 = (0 : Felt) ∨
                            (1 : Felt) - data8 = (0 : Felt))))[props][{ name := "%116" : PropVar }] ←
                      ((((((((((data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) +
                                                                            data5 * (5 : Felt) +
                                                                          data6 * (6 : Felt) +
                                                                        data7 * (7 : Felt) +
                                                                      data8 * (8 : Felt) +
                                                                    data9 * (9 : Felt) +
                                                                  data10 * (10 : Felt) +
                                                                data11 * (11 : Felt) +
                                                              data12 * (12 : Felt) +
                                                            data13 * (13 : Felt) +
                                                          data14 * (14 : Felt) +
                                                        data15 * (15 : Felt) +
                                                      data16 * (16 : Felt) +
                                                    data17 * (17 : Felt) +
                                                  data18 * (18 : Felt) +
                                                data19 * (19 : Felt) -
                                              code0 =
                                            (0 : Felt) ∧
                                          (data0 = (0 : Felt) ∨ (1 : Felt) - data0 = (0 : Felt))) ∧
                                        (data1 = (0 : Felt) ∨ (1 : Felt) - data1 = (0 : Felt))) ∧
                                      (data2 = (0 : Felt) ∨ (1 : Felt) - data2 = (0 : Felt))) ∧
                                    (data3 = (0 : Felt) ∨ (1 : Felt) - data3 = (0 : Felt))) ∧
                                  (data4 = (0 : Felt) ∨ (1 : Felt) - data4 = (0 : Felt))) ∧
                                (data5 = (0 : Felt) ∨ (1 : Felt) - data5 = (0 : Felt))) ∧
                              (data6 = (0 : Felt) ∨ (1 : Felt) - data6 = (0 : Felt))) ∧
                            (data7 = (0 : Felt) ∨ (1 : Felt) - data7 = (0 : Felt))) ∧
                          (data8 = (0 : Felt) ∨ (1 : Felt) - data8 = (0 : Felt))) ∧
                        (data9 = (0 : Felt) ∨ (1 : Felt) - data9 = (0 : Felt))))[props][{ name := "%120" : PropVar }] ←
                    (((((((((((data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) +
                                                                            data5 * (5 : Felt) +
                                                                          data6 * (6 : Felt) +
                                                                        data7 * (7 : Felt) +
                                                                      data8 * (8 : Felt) +
                                                                    data9 * (9 : Felt) +
                                                                  data10 * (10 : Felt) +
                                                                data11 * (11 : Felt) +
                                                              data12 * (12 : Felt) +
                                                            data13 * (13 : Felt) +
                                                          data14 * (14 : Felt) +
                                                        data15 * (15 : Felt) +
                                                      data16 * (16 : Felt) +
                                                    data17 * (17 : Felt) +
                                                  data18 * (18 : Felt) +
                                                data19 * (19 : Felt) -
                                              code0 =
                                            (0 : Felt) ∧
                                          (data0 = (0 : Felt) ∨ (1 : Felt) - data0 = (0 : Felt))) ∧
                                        (data1 = (0 : Felt) ∨ (1 : Felt) - data1 = (0 : Felt))) ∧
                                      (data2 = (0 : Felt) ∨ (1 : Felt) - data2 = (0 : Felt))) ∧
                                    (data3 = (0 : Felt) ∨ (1 : Felt) - data3 = (0 : Felt))) ∧
                                  (data4 = (0 : Felt) ∨ (1 : Felt) - data4 = (0 : Felt))) ∧
                                (data5 = (0 : Felt) ∨ (1 : Felt) - data5 = (0 : Felt))) ∧
                              (data6 = (0 : Felt) ∨ (1 : Felt) - data6 = (0 : Felt))) ∧
                            (data7 = (0 : Felt) ∨ (1 : Felt) - data7 = (0 : Felt))) ∧
                          (data8 = (0 : Felt) ∨ (1 : Felt) - data8 = (0 : Felt))) ∧
                        (data9 = (0 : Felt) ∨ (1 : Felt) - data9 = (0 : Felt))) ∧
                      (data10 = (0 : Felt) ∨ (1 : Felt) - data10 = (0 : Felt))))[props][{ name := "%124" : PropVar }] ←
                  ((((((((((((data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) +
                                                                            data5 * (5 : Felt) +
                                                                          data6 * (6 : Felt) +
                                                                        data7 * (7 : Felt) +
                                                                      data8 * (8 : Felt) +
                                                                    data9 * (9 : Felt) +
                                                                  data10 * (10 : Felt) +
                                                                data11 * (11 : Felt) +
                                                              data12 * (12 : Felt) +
                                                            data13 * (13 : Felt) +
                                                          data14 * (14 : Felt) +
                                                        data15 * (15 : Felt) +
                                                      data16 * (16 : Felt) +
                                                    data17 * (17 : Felt) +
                                                  data18 * (18 : Felt) +
                                                data19 * (19 : Felt) -
                                              code0 =
                                            (0 : Felt) ∧
                                          (data0 = (0 : Felt) ∨ (1 : Felt) - data0 = (0 : Felt))) ∧
                                        (data1 = (0 : Felt) ∨ (1 : Felt) - data1 = (0 : Felt))) ∧
                                      (data2 = (0 : Felt) ∨ (1 : Felt) - data2 = (0 : Felt))) ∧
                                    (data3 = (0 : Felt) ∨ (1 : Felt) - data3 = (0 : Felt))) ∧
                                  (data4 = (0 : Felt) ∨ (1 : Felt) - data4 = (0 : Felt))) ∧
                                (data5 = (0 : Felt) ∨ (1 : Felt) - data5 = (0 : Felt))) ∧
                              (data6 = (0 : Felt) ∨ (1 : Felt) - data6 = (0 : Felt))) ∧
                            (data7 = (0 : Felt) ∨ (1 : Felt) - data7 = (0 : Felt))) ∧
                          (data8 = (0 : Felt) ∨ (1 : Felt) - data8 = (0 : Felt))) ∧
                        (data9 = (0 : Felt) ∨ (1 : Felt) - data9 = (0 : Felt))) ∧
                      (data10 = (0 : Felt) ∨ (1 : Felt) - data10 = (0 : Felt))) ∧
                    (data11 = (0 : Felt) ∨ (1 : Felt) - data11 = (0 : Felt))))[props][{ name := "%128" : PropVar }] ←
                (((((((((((((data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) + data5 * (5 : Felt) +
                                                                          data6 * (6 : Felt) +
                                                                        data7 * (7 : Felt) +
                                                                      data8 * (8 : Felt) +
                                                                    data9 * (9 : Felt) +
                                                                  data10 * (10 : Felt) +
                                                                data11 * (11 : Felt) +
                                                              data12 * (12 : Felt) +
                                                            data13 * (13 : Felt) +
                                                          data14 * (14 : Felt) +
                                                        data15 * (15 : Felt) +
                                                      data16 * (16 : Felt) +
                                                    data17 * (17 : Felt) +
                                                  data18 * (18 : Felt) +
                                                data19 * (19 : Felt) -
                                              code0 =
                                            (0 : Felt) ∧
                                          (data0 = (0 : Felt) ∨ (1 : Felt) - data0 = (0 : Felt))) ∧
                                        (data1 = (0 : Felt) ∨ (1 : Felt) - data1 = (0 : Felt))) ∧
                                      (data2 = (0 : Felt) ∨ (1 : Felt) - data2 = (0 : Felt))) ∧
                                    (data3 = (0 : Felt) ∨ (1 : Felt) - data3 = (0 : Felt))) ∧
                                  (data4 = (0 : Felt) ∨ (1 : Felt) - data4 = (0 : Felt))) ∧
                                (data5 = (0 : Felt) ∨ (1 : Felt) - data5 = (0 : Felt))) ∧
                              (data6 = (0 : Felt) ∨ (1 : Felt) - data6 = (0 : Felt))) ∧
                            (data7 = (0 : Felt) ∨ (1 : Felt) - data7 = (0 : Felt))) ∧
                          (data8 = (0 : Felt) ∨ (1 : Felt) - data8 = (0 : Felt))) ∧
                        (data9 = (0 : Felt) ∨ (1 : Felt) - data9 = (0 : Felt))) ∧
                      (data10 = (0 : Felt) ∨ (1 : Felt) - data10 = (0 : Felt))) ∧
                    (data11 = (0 : Felt) ∨ (1 : Felt) - data11 = (0 : Felt))) ∧
                  (data12 = (0 : Felt) ∨ (1 : Felt) - data12 = (0 : Felt))))[props][{ name := "%132" : PropVar }] ←
              ((((((((((((((data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) + data5 * (5 : Felt) +
                                                                          data6 * (6 : Felt) +
                                                                        data7 * (7 : Felt) +
                                                                      data8 * (8 : Felt) +
                                                                    data9 * (9 : Felt) +
                                                                  data10 * (10 : Felt) +
                                                                data11 * (11 : Felt) +
                                                              data12 * (12 : Felt) +
                                                            data13 * (13 : Felt) +
                                                          data14 * (14 : Felt) +
                                                        data15 * (15 : Felt) +
                                                      data16 * (16 : Felt) +
                                                    data17 * (17 : Felt) +
                                                  data18 * (18 : Felt) +
                                                data19 * (19 : Felt) -
                                              code0 =
                                            (0 : Felt) ∧
                                          (data0 = (0 : Felt) ∨ (1 : Felt) - data0 = (0 : Felt))) ∧
                                        (data1 = (0 : Felt) ∨ (1 : Felt) - data1 = (0 : Felt))) ∧
                                      (data2 = (0 : Felt) ∨ (1 : Felt) - data2 = (0 : Felt))) ∧
                                    (data3 = (0 : Felt) ∨ (1 : Felt) - data3 = (0 : Felt))) ∧
                                  (data4 = (0 : Felt) ∨ (1 : Felt) - data4 = (0 : Felt))) ∧
                                (data5 = (0 : Felt) ∨ (1 : Felt) - data5 = (0 : Felt))) ∧
                              (data6 = (0 : Felt) ∨ (1 : Felt) - data6 = (0 : Felt))) ∧
                            (data7 = (0 : Felt) ∨ (1 : Felt) - data7 = (0 : Felt))) ∧
                          (data8 = (0 : Felt) ∨ (1 : Felt) - data8 = (0 : Felt))) ∧
                        (data9 = (0 : Felt) ∨ (1 : Felt) - data9 = (0 : Felt))) ∧
                      (data10 = (0 : Felt) ∨ (1 : Felt) - data10 = (0 : Felt))) ∧
                    (data11 = (0 : Felt) ∨ (1 : Felt) - data11 = (0 : Felt))) ∧
                  (data12 = (0 : Felt) ∨ (1 : Felt) - data12 = (0 : Felt))) ∧
                (data13 = (0 : Felt) ∨ (1 : Felt) - data13 = (0 : Felt))))[felts][{ name := "%133" : FeltVar }] ←
            data0 + data1 + data2 + data3 + data4 + data5 + data6 + data7 + data8 + data9 + data10 + data11 + data12 +
              data13)[felts][{ name := "%135" : FeltVar }] ←
          data14 * ((1 : Felt) - data14)))  := by
    rewrite [part33_cumulative_wp]
    rewrite [part34_updates_opaque]
    unfold part33_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part33_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths, State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.OneHot20.Constraints.WP