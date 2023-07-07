import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart5

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part6 on st
def part6_state (st: State) : State :=
  
        ((((st[props][{ name := "%28" }] ←
                (Option.get! (State.props st { name := "%6" }) ∧
                  Option.get! (State.felts st { name := "%27" }) = (0 : Felt)))["%30"] ←ₛ
              getImpl st { name := "data" } (0 : Back) (4 : ℕ))[felts][{ name := "%31" }] ←
            Option.get!
                (State.felts
                  ((st[props][{ name := "%28" }] ←
                      (Option.get! (State.props st { name := "%6" }) ∧
                        Option.get! (State.felts st { name := "%27" }) = (0 : Felt)))["%30"] ←ₛ
                    getImpl st { name := "data" } (0 : Back) (4 : ℕ))
                  { name := "%30" }) *
              Option.get! (State.felts st { name := "%4" }))["%33"] ←ₛ
          getImpl
            (st[props][{ name := "%28" }] ←
              (Option.get! (State.props st { name := "%6" }) ∧
                Option.get! (State.felts st { name := "%27" }) = (0 : Felt)))
            { name := "data" } (0 : Back) (2 : ℕ)) 

def part6_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (st) ⟨"%27"⟩) ⟨"%30"⟩

-- Run the program from part6 onwards by using part6_state rather than Code.part6
def part6_state_update (st: State): State :=
  Γ (part6_drops (part6_state st)) ⟦Code.part7;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;Code.part8;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;Code.part9;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;Code.part10;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part11;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;Code.part12;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part13;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩⟧

-- Prove that substituting part6_state for Code.part6 produces the same result
lemma part6_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part6;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;Code.part7;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;Code.part8;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;Code.part9;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;Code.part10;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part11;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;Code.part12;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part13;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩) st) ↔
  Code.getReturn (part6_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;Code.part7;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;Code.part8;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;Code.part9;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;Code.part10;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part11;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;Code.part12;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part13;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩) = prog
  unfold Code.part6
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part6_state_update part6_drops part6_state
  rfl

lemma part6_updates_opaque {st : State} : 
  Code.getReturn (part5_state_update st) ↔
  Code.getReturn (part6_state_update (part5_drops (part5_state st))) := by
  simp [part5_state_update, part6_wp]

lemma part6_cumulative_wp {x0 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19: Felt} :
  Code.run (start_state [x0] ([y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19])) ↔
  Code.getReturn
      (part6_state_update
        ({
            buffers :=
              ((((((((({
                                    buffers :=
                                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                                          [[some y0, some y1, some y2, some y3, some y4, some y5, some y6, some y7,
                                              some y8, some y9, some y10, some y11, some y12, some y13, some y14,
                                              some y15, some y16, some y17, some y18, some y19]])[{ name := "code" }] ←ₘ
                                        [[some x0]],
                                    bufferWidths :=
                                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ (20 : ℕ))[{ name := "code" }] ←ₘ
                                        (1 : ℕ),
                                    constraints := [], cycle := (0 : ℕ), felts := Map.empty, isFailed := false,
                                    props := Map.empty,
                                    vars := [{ name := "code" }, { name := "data" }] }[props][{ name := "%6" }] ←
                                  True)[felts][{ name := "%4" }] ←
                                (4 : Felt))[felts][{ name := "%2" }] ←
                              (8 : Felt))[felts][{ name := "%1" }] ←
                            (16 : Felt))[felts][{ name := "%3" }] ←
                          (2 : Felt))[felts][{ name := "%25" }] ←
                        (y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) *
                          (2 : Felt))[felts][{ name := "%11" }] ←
                      y13)[felts][{ name := "%26" }] ←
                    (y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) * (2 : Felt) +
                      y13)["%10"] ←ₛ
                  none).buffers,
            bufferWidths :=
              ((((((((({
                                    buffers :=
                                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                                          [[some y0, some y1, some y2, some y3, some y4, some y5, some y6, some y7,
                                              some y8, some y9, some y10, some y11, some y12, some y13, some y14,
                                              some y15, some y16, some y17, some y18, some y19]])[{ name := "code" }] ←ₘ
                                        [[some x0]],
                                    bufferWidths :=
                                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ (20 : ℕ))[{ name := "code" }] ←ₘ
                                        (1 : ℕ),
                                    constraints := [], cycle := (0 : ℕ), felts := Map.empty, isFailed := false,
                                    props := Map.empty,
                                    vars := [{ name := "code" }, { name := "data" }] }[props][{ name := "%6" }] ←
                                  True)[felts][{ name := "%4" }] ←
                                (4 : Felt))[felts][{ name := "%2" }] ←
                              (8 : Felt))[felts][{ name := "%1" }] ←
                            (16 : Felt))[felts][{ name := "%3" }] ←
                          (2 : Felt))[felts][{ name := "%25" }] ←
                        (y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) *
                          (2 : Felt))[felts][{ name := "%11" }] ←
                      y13)[felts][{ name := "%26" }] ←
                    (y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) * (2 : Felt) +
                      y13)["%10"] ←ₛ
                  none).bufferWidths,
            constraints :=
              ((((((((({
                                    buffers :=
                                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                                          [[some y0, some y1, some y2, some y3, some y4, some y5, some y6, some y7,
                                              some y8, some y9, some y10, some y11, some y12, some y13, some y14,
                                              some y15, some y16, some y17, some y18, some y19]])[{ name := "code" }] ←ₘ
                                        [[some x0]],
                                    bufferWidths :=
                                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ (20 : ℕ))[{ name := "code" }] ←ₘ
                                        (1 : ℕ),
                                    constraints := [], cycle := (0 : ℕ), felts := Map.empty, isFailed := false,
                                    props := Map.empty,
                                    vars := [{ name := "code" }, { name := "data" }] }[props][{ name := "%6" }] ←
                                  True)[felts][{ name := "%4" }] ←
                                (4 : Felt))[felts][{ name := "%2" }] ←
                              (8 : Felt))[felts][{ name := "%1" }] ←
                            (16 : Felt))[felts][{ name := "%3" }] ←
                          (2 : Felt))[felts][{ name := "%25" }] ←
                        (y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) *
                          (2 : Felt))[felts][{ name := "%11" }] ←
                      y13)[felts][{ name := "%26" }] ←
                    (y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) * (2 : Felt) +
                      y13)["%10"] ←ₛ
                  none).constraints,
            cycle :=
              ((((((((({
                                    buffers :=
                                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                                          [[some y0, some y1, some y2, some y3, some y4, some y5, some y6, some y7,
                                              some y8, some y9, some y10, some y11, some y12, some y13, some y14,
                                              some y15, some y16, some y17, some y18, some y19]])[{ name := "code" }] ←ₘ
                                        [[some x0]],
                                    bufferWidths :=
                                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ (20 : ℕ))[{ name := "code" }] ←ₘ
                                        (1 : ℕ),
                                    constraints := [], cycle := (0 : ℕ), felts := Map.empty, isFailed := false,
                                    props := Map.empty,
                                    vars := [{ name := "code" }, { name := "data" }] }[props][{ name := "%6" }] ←
                                  True)[felts][{ name := "%4" }] ←
                                (4 : Felt))[felts][{ name := "%2" }] ←
                              (8 : Felt))[felts][{ name := "%1" }] ←
                            (16 : Felt))[felts][{ name := "%3" }] ←
                          (2 : Felt))[felts][{ name := "%25" }] ←
                        (y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) *
                          (2 : Felt))[felts][{ name := "%11" }] ←
                      y13)[felts][{ name := "%26" }] ←
                    (y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) * (2 : Felt) +
                      y13)["%10"] ←ₛ
                  none).cycle,
            felts :=
              Map.drop
                (Map.drop
                  (Map.drop
                    (Map.drop
                      ((((((((({
                                            buffers :=
                                              ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                                                  [[some y0, some y1, some y2, some y3, some y4, some y5, some y6,
                                                      some y7, some y8, some y9, some y10, some y11, some y12, some y13,
                                                      some y14, some y15, some y16, some y17, some y18,
                                                      some y19]])[{ name := "code" }] ←ₘ
                                                [[some x0]],
                                            bufferWidths :=
                                              ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                                                  (20 : ℕ))[{ name := "code" }] ←ₘ
                                                (1 : ℕ),
                                            constraints := [], cycle := (0 : ℕ), felts := Map.empty, isFailed := false,
                                            props := Map.empty,
                                            vars :=
                                              [{ name := "code" }, { name := "data" }] }[props][{ name := "%6" }] ←
                                          True)[felts][{ name := "%4" }] ←
                                        (4 : Felt))[felts][{ name := "%2" }] ←
                                      (8 : Felt))[felts][{ name := "%1" }] ←
                                    (16 : Felt))[felts][{ name := "%3" }] ←
                                  (2 : Felt))[felts][{ name := "%25" }] ←
                                (y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) *
                                  (2 : Felt))[felts][{ name := "%11" }] ←
                              y13)[felts][{ name := "%26" }] ←
                            (y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) *
                                (2 : Felt) +
                              y13)["%10"] ←ₛ
                          none).felts
                      { name := "%25" })
                    { name := "%11" })
                  { name := "%26" })
                { name := "%10" },
            isFailed :=
              ((((((((({
                                    buffers :=
                                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                                          [[some y0, some y1, some y2, some y3, some y4, some y5, some y6, some y7,
                                              some y8, some y9, some y10, some y11, some y12, some y13, some y14,
                                              some y15, some y16, some y17, some y18, some y19]])[{ name := "code" }] ←ₘ
                                        [[some x0]],
                                    bufferWidths :=
                                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ (20 : ℕ))[{ name := "code" }] ←ₘ
                                        (1 : ℕ),
                                    constraints := [], cycle := (0 : ℕ), felts := Map.empty, isFailed := false,
                                    props := Map.empty,
                                    vars := [{ name := "code" }, { name := "data" }] }[props][{ name := "%6" }] ←
                                  True)[felts][{ name := "%4" }] ←
                                (4 : Felt))[felts][{ name := "%2" }] ←
                              (8 : Felt))[felts][{ name := "%1" }] ←
                            (16 : Felt))[felts][{ name := "%3" }] ←
                          (2 : Felt))[felts][{ name := "%25" }] ←
                        (y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) *
                          (2 : Felt))[felts][{ name := "%11" }] ←
                      y13)[felts][{ name := "%26" }] ←
                    (y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) * (2 : Felt) +
                      y13)["%10"] ←ₛ
                  none).isFailed,
            props :=
              ((((((((({
                                    buffers :=
                                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                                          [[some y0, some y1, some y2, some y3, some y4, some y5, some y6, some y7,
                                              some y8, some y9, some y10, some y11, some y12, some y13, some y14,
                                              some y15, some y16, some y17, some y18, some y19]])[{ name := "code" }] ←ₘ
                                        [[some x0]],
                                    bufferWidths :=
                                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ (20 : ℕ))[{ name := "code" }] ←ₘ
                                        (1 : ℕ),
                                    constraints := [], cycle := (0 : ℕ), felts := Map.empty, isFailed := false,
                                    props := Map.empty,
                                    vars := [{ name := "code" }, { name := "data" }] }[props][{ name := "%6" }] ←
                                  True)[felts][{ name := "%4" }] ←
                                (4 : Felt))[felts][{ name := "%2" }] ←
                              (8 : Felt))[felts][{ name := "%1" }] ←
                            (16 : Felt))[felts][{ name := "%3" }] ←
                          (2 : Felt))[felts][{ name := "%25" }] ←
                        (y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) *
                          (2 : Felt))[felts][{ name := "%11" }] ←
                      y13)[felts][{ name := "%26" }] ←
                    (y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) * (2 : Felt) +
                      y13)["%10"] ←ₛ
                  none).props,
            vars :=
              ((((((((({
                                    buffers :=
                                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                                          [[some y0, some y1, some y2, some y3, some y4, some y5, some y6, some y7,
                                              some y8, some y9, some y10, some y11, some y12, some y13, some y14,
                                              some y15, some y16, some y17, some y18, some y19]])[{ name := "code" }] ←ₘ
                                        [[some x0]],
                                    bufferWidths :=
                                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ (20 : ℕ))[{ name := "code" }] ←ₘ
                                        (1 : ℕ),
                                    constraints := [], cycle := (0 : ℕ), felts := Map.empty, isFailed := false,
                                    props := Map.empty,
                                    vars := [{ name := "code" }, { name := "data" }] }[props][{ name := "%6" }] ←
                                  True)[felts][{ name := "%4" }] ←
                                (4 : Felt))[felts][{ name := "%2" }] ←
                              (8 : Felt))[felts][{ name := "%1" }] ←
                            (16 : Felt))[felts][{ name := "%3" }] ←
                          (2 : Felt))[felts][{ name := "%25" }] ←
                        (y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) *
                          (2 : Felt))[felts][{ name := "%11" }] ←
                      y13)[felts][{ name := "%26" }] ←
                    (y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) * (2 : Felt) +
                      y13)["%10"] ←ₛ
                  none).vars }[felts][{ name := "%27" }] ←
          (match
              State.felts
                ((((((((({
                                    buffers :=
                                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                                          [[some y0, some y1, some y2, some y3, some y4, some y5, some y6, some y7,
                                              some y8, some y9, some y10, some y11, some y12, some y13, some y14,
                                              some y15, some y16, some y17, some y18, some y19]])[{ name := "code" }] ←ₘ
                                        [[some x0]],
                                    bufferWidths :=
                                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ (20 : ℕ))[{ name := "code" }] ←ₘ
                                        (1 : ℕ),
                                    constraints := [], cycle := (0 : ℕ), felts := Map.empty, isFailed := false,
                                    props := Map.empty,
                                    vars := [{ name := "code" }, { name := "data" }] }[props][{ name := "%6" }] ←
                                  True)[felts][{ name := "%4" }] ←
                                (4 : Felt))[felts][{ name := "%2" }] ←
                              (8 : Felt))[felts][{ name := "%1" }] ←
                            (16 : Felt))[felts][{ name := "%3" }] ←
                          (2 : Felt))[felts][{ name := "%25" }] ←
                        (y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) *
                          (2 : Felt))[felts][{ name := "%11" }] ←
                      y13)[felts][{ name := "%26" }] ←
                    (y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) * (2 : Felt) +
                      y13)["%10"] ←ₛ
                  none)
                { name := "%10" } with
            | some x => x
            | none =>
              panicWithPosWithDecl "Init.Data.Option.BasicAux" "Option.get!" (16 : ℕ) (14 : ℕ) "value is none") -
            ((y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) * (2 : Felt) + y13)))  := by
    rewrite [part5_cumulative_wp]
    rewrite [part6_updates_opaque]
    unfold part5_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part5_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

end Risc0.ComputeDecode.Constraints.WP