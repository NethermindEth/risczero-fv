import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart30

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part31 on st
def part31_state (st: State) : State :=
  
        ((((st[props][{ name := "%124" : PropVar }] ←
                ((st.props { name := "%120" : PropVar }).get! ∧
                  (st.felts { name := "%123" : FeltVar }).get! = (0 : Felt)))[felts][{ name := "%125" : FeltVar }] ←
              (st.felts { name := "%121" : FeltVar }).get! +
                (st.felts { name := "%49" : FeltVar }).get!)[felts][{ name := "%126" : FeltVar }] ←
            (st.felts { name := "%0" : FeltVar }).get! -
              (st.felts { name := "%52" : FeltVar }).get!)[felts][{ name := "%127" : FeltVar }] ←
          (st.felts { name := "%52" : FeltVar }).get! *
            ((st.felts { name := "%0" : FeltVar }).get! - (st.felts { name := "%52" : FeltVar }).get!)) 

def part31_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%49"⟩) ⟨"%121"⟩) ⟨"%123"⟩) ⟨"%126"⟩

-- Run the program from part31 onwards by using part31_state rather than Code.part31
def part31_state_update (st: State): State :=
  Γ (part31_drops (part31_state st)) ⟦Code.part32;dropfelt ⟨"%52"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%130"⟩;Code.part33;dropfelt ⟨"%55"⟩;dropfelt ⟨"%129"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%134"⟩;Code.part34;dropfelt ⟨"%58"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%135"⟩;dropfelt ⟨"%138"⟩;Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%73"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩⟧

-- Prove that substituting part31_state for Code.part31 produces the same result
lemma part31_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part31;dropfelt ⟨"%49"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%123"⟩;dropfelt ⟨"%126"⟩;Code.part32;dropfelt ⟨"%52"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%130"⟩;Code.part33;dropfelt ⟨"%55"⟩;dropfelt ⟨"%129"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%134"⟩;Code.part34;dropfelt ⟨"%58"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%135"⟩;dropfelt ⟨"%138"⟩;Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%73"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩) st) ↔
  Code.getReturn (part31_state_update st) := by
  unfold MLIR.runProgram; try simp only
  generalize eq : (dropfelt ⟨"%49"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%123"⟩;dropfelt ⟨"%126"⟩;Code.part32;dropfelt ⟨"%52"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%130"⟩;Code.part33;dropfelt ⟨"%55"⟩;dropfelt ⟨"%129"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%134"⟩;Code.part34;dropfelt ⟨"%58"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%135"⟩;dropfelt ⟨"%138"⟩;Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%73"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩) = prog
  unfold Code.part31
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part31_state_update part31_drops part31_state
  rfl

lemma part31_updates_opaque {st : State} : 
  Code.getReturn (part30_state_update st) ↔
  Code.getReturn (part31_state_update (part30_drops (part30_state st))) := by
  try simp [part30_state_update, part31_wp]

lemma part31_cumulative_wp {code0 data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 data18 data19: Felt} :
  Code.run (start_state ([code0]) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19])) ↔
  Code.getReturn
      (part31_state_update
        ((((((((((((((((((((((((({
                                                            buffers :=
                                                              (Map.empty[{ name := "data" : BufferVar }] ←ₘ
                                                                  [[some data0, some data1, some data2, some data3,
                                                                      some data4, some data5, some data6, some data7,
                                                                      some data8, some data9, some data10, some data11,
                                                                      some data12, some data13, some data14,
                                                                      some data15, some data16, some data17,
                                                                      some data18,
                                                                      some data19]])[{ name := "code" : BufferVar }] ←ₘ
                                                                [[some code0]],
                                                            bufferWidths :=
                                                              (Map.empty[{ name := "data" : BufferVar }] ←ₘ
                                                                  (20 : ℕ))[{ name := "code" : BufferVar }] ←ₘ
                                                                (1 : ℕ),
                                                            cycle := (0 : ℕ), felts := Map.empty, isFailed := False,
                                                            props := Map.empty,
                                                            vars :=
                                                              [{ name := "code" : BufferVar },
                                                                { name := "data" :
                                                                  BufferVar }] }[props][{ name := "%19" : PropVar }] ←
                                                          True)[felts][{ name := "%49" : FeltVar }] ←
                                                        data11)[felts][{ name := "%52" : FeltVar }] ←
                                                      data12)[felts][{ name := "%55" : FeltVar }] ←
                                                    data13)[felts][{ name := "%58" : FeltVar }] ←
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
                      (((((((data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) + data5 * (5 : Felt) +
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
                        (data6 = (0 : Felt) ∨ (1 : Felt) - data6 = (0 : Felt))))[props][{ name := "%108" : PropVar }] ←
                    ((((((((data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) + data5 * (5 : Felt) +
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
                      (data7 = (0 : Felt) ∨ (1 : Felt) - data7 = (0 : Felt))))[props][{ name := "%112" : PropVar }] ←
                  (((((((((data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) + data5 * (5 : Felt) +
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
                    (data8 = (0 : Felt) ∨ (1 : Felt) - data8 = (0 : Felt))))[props][{ name := "%116" : PropVar }] ←
                ((((((((((data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) + data5 * (5 : Felt) +
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
              (((((((((((data1 + data2 * (2 : Felt) + data3 * (3 : Felt) + data4 * (4 : Felt) + data5 * (5 : Felt) +
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
                (data10 = (0 : Felt) ∨ (1 : Felt) - data10 = (0 : Felt))))[felts][{ name := "%121" : FeltVar }] ←
            data0 + data1 + data2 + data3 + data4 + data5 + data6 + data7 + data8 + data9 +
              data10)[felts][{ name := "%123" : FeltVar }] ←
          data11 * ((1 : Felt) - data11)))  := by
    rewrite [part30_cumulative_wp]
    rewrite [part31_updates_opaque]
    unfold part30_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part30_drops
    -- 4 drops
    try simp [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    try simp [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    try simp [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- try simp [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.OneHot20.Constraints.WP