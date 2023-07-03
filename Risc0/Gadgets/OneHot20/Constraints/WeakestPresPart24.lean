import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart23

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part24 on st
def part24_state (st: State) : State :=
  
        ((((st[props][{ name := "%96" }] ←
                (Option.get! (State.props st { name := "%92" }) ∧
                  Option.get! (State.felts st { name := "%95" }) = 0))[felts][{ name := "%97" }] ←
              Option.get! (State.felts st { name := "%93" }) +
                Option.get! (State.felts st { name := "%28" }))[felts][{ name := "%98" }] ←
            Option.get! (State.felts st { name := "%0" }) -
              Option.get! (State.felts st { name := "%31" }))[felts][{ name := "%99" }] ←
          Option.get! (State.felts st { name := "%31" }) *
            (Option.get! (State.felts st { name := "%0" }) - Option.get! (State.felts st { name := "%31" }))) 

def part24_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%28"⟩) ⟨"%93"⟩) ⟨"%95"⟩) ⟨"%98"⟩

-- Run the program from part24 onwards by using part24_state rather than Code.part24
def part24_state_update (st: State): State :=
  Γ (part24_drops (part24_state st)) ⟦Code.part25;dropfelt ⟨"%31"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%102"⟩;Code.part26;dropfelt ⟨"%34"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%106"⟩;Code.part27;dropfelt ⟨"%37"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%110"⟩;Code.part28;dropfelt ⟨"%40"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%111"⟩;dropfelt ⟨"%114"⟩;Code.part29;dropfelt ⟨"%43"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%118"⟩;Code.part30;dropfelt ⟨"%46"⟩;dropfelt ⟨"%117"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%122"⟩;Code.part31;dropfelt ⟨"%49"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%123"⟩;dropfelt ⟨"%126"⟩;Code.part32;dropfelt ⟨"%52"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%130"⟩;Code.part33;dropfelt ⟨"%55"⟩;dropfelt ⟨"%129"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%134"⟩;Code.part34;dropfelt ⟨"%58"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%135"⟩;dropfelt ⟨"%138"⟩;Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%19"⟩;dropfelt ⟨"%73"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%108"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%120"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%132"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%140"⟩;dropfelt ⟨"%144"⟩;dropfelt ⟨"%148"⟩;dropfelt ⟨"%152"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;dropfelt ⟨"%159"⟩⟧

-- Prove that substituting part24_state for Code.part24 produces the same result
lemma part24_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part24;dropfelt ⟨"%28"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%98"⟩;Code.part25;dropfelt ⟨"%31"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%102"⟩;Code.part26;dropfelt ⟨"%34"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%106"⟩;Code.part27;dropfelt ⟨"%37"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%110"⟩;Code.part28;dropfelt ⟨"%40"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%111"⟩;dropfelt ⟨"%114"⟩;Code.part29;dropfelt ⟨"%43"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%118"⟩;Code.part30;dropfelt ⟨"%46"⟩;dropfelt ⟨"%117"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%122"⟩;Code.part31;dropfelt ⟨"%49"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%123"⟩;dropfelt ⟨"%126"⟩;Code.part32;dropfelt ⟨"%52"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%130"⟩;Code.part33;dropfelt ⟨"%55"⟩;dropfelt ⟨"%129"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%134"⟩;Code.part34;dropfelt ⟨"%58"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%135"⟩;dropfelt ⟨"%138"⟩;Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%19"⟩;dropfelt ⟨"%73"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%108"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%120"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%132"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%140"⟩;dropfelt ⟨"%144"⟩;dropfelt ⟨"%148"⟩;dropfelt ⟨"%152"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;dropfelt ⟨"%159"⟩) st) ↔
  Code.getReturn (part24_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%28"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%98"⟩;Code.part25;dropfelt ⟨"%31"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%102"⟩;Code.part26;dropfelt ⟨"%34"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%106"⟩;Code.part27;dropfelt ⟨"%37"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%107"⟩;dropfelt ⟨"%110"⟩;Code.part28;dropfelt ⟨"%40"⟩;dropfelt ⟨"%109"⟩;dropfelt ⟨"%111"⟩;dropfelt ⟨"%114"⟩;Code.part29;dropfelt ⟨"%43"⟩;dropfelt ⟨"%113"⟩;dropfelt ⟨"%115"⟩;dropfelt ⟨"%118"⟩;Code.part30;dropfelt ⟨"%46"⟩;dropfelt ⟨"%117"⟩;dropfelt ⟨"%119"⟩;dropfelt ⟨"%122"⟩;Code.part31;dropfelt ⟨"%49"⟩;dropfelt ⟨"%121"⟩;dropfelt ⟨"%123"⟩;dropfelt ⟨"%126"⟩;Code.part32;dropfelt ⟨"%52"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%130"⟩;Code.part33;dropfelt ⟨"%55"⟩;dropfelt ⟨"%129"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%134"⟩;Code.part34;dropfelt ⟨"%58"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%135"⟩;dropfelt ⟨"%138"⟩;Code.part35;dropfelt ⟨"%61"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%139"⟩;dropfelt ⟨"%142"⟩;Code.part36;dropfelt ⟨"%64"⟩;dropfelt ⟨"%141"⟩;dropfelt ⟨"%143"⟩;dropfelt ⟨"%146"⟩;Code.part37;dropfelt ⟨"%67"⟩;dropfelt ⟨"%145"⟩;dropfelt ⟨"%147"⟩;dropfelt ⟨"%150"⟩;Code.part38;dropfelt ⟨"%70"⟩;dropfelt ⟨"%149"⟩;dropfelt ⟨"%151"⟩;dropfelt ⟨"%154"⟩;Code.part39;dropfelt ⟨"%19"⟩;dropfelt ⟨"%73"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%108"⟩;dropfelt ⟨"%112"⟩;dropfelt ⟨"%116"⟩;dropfelt ⟨"%120"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%132"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%140"⟩;dropfelt ⟨"%144"⟩;dropfelt ⟨"%148"⟩;dropfelt ⟨"%152"⟩;dropfelt ⟨"%153"⟩;dropfelt ⟨"%155"⟩;dropfelt ⟨"%156"⟩;dropfelt ⟨"%157"⟩;dropfelt ⟨"%158"⟩;dropfelt ⟨"%159"⟩) = prog
  unfold Code.part24
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part24_state_update part24_drops part24_state
  rfl

lemma part24_updates_opaque {st : State} : 
  Code.getReturn (part23_state_update st) ↔
  Code.getReturn (part24_state_update (part23_drops (part23_state st))) := by
  simp [part23_state_update, part24_wp]

lemma part24_cumulative_wp {x0 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19: Felt} :
  Code.run (start_state [x0] ([y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19])) ↔
  Code.getReturn
      (part24_state_update
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
                                                          True)[felts][{ name := "%28" }] ←
                                                        y4)[felts][{ name := "%31" }] ←
                                                      y5)[felts][{ name := "%34" }] ←
                                                    y6)[felts][{ name := "%37" }] ←
                                                  y7)[felts][{ name := "%40" }] ←
                                                y8)[felts][{ name := "%43" }] ←
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
                        y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 + y10 * 10 +
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
                    (y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 + y10 * 10 + y11 * 11 +
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
                  ((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 + y10 * 10 + y11 * 11 +
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
                (((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 + y10 * 10 + y11 * 11 +
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
              ((((y1 + y2 * 2 + y3 * 3 + y4 * 4 + y5 * 5 + y6 * 6 + y7 * 7 + y8 * 8 + y9 * 9 + y10 * 10 + y11 * 11 +
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
                (y3 = 0 ∨ 1 - y3 = 0)))[felts][{ name := "%93" }] ←
            y0 + y1 + y2 + y3)[felts][{ name := "%95" }] ←
          y4 * (1 - y4)))  := by
    rewrite [part23_cumulative_wp]
    rewrite [part24_updates_opaque]
    unfold part23_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part23_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

end Risc0.OneHot20.Constraints.WP