import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart27

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part28 on st
def part28_state (st: State) : State :=
  
          ((((st[felts][{ name := "%61" }] ←
                  Option.get! (State.felts st { name := "%60" }) +
                    Option.get! (State.felts st { name := "%58" }))[felts][{ name := "%62" }] ←
                (Option.get! (State.felts st { name := "%60" }) + Option.get! (State.felts st { name := "%58" })) *
                  Option.get! (State.felts st { name := "%15" }))["%63"] ←ₛ
              getImpl st { name := "data" } (0 : Back) (14 : ℕ))[felts][{ name := "%64" }] ←
            Option.get!
                (State.felts
                  (((st[felts][{ name := "%61" }] ←
                        Option.get! (State.felts st { name := "%60" }) +
                          Option.get! (State.felts st { name := "%58" }))[felts][{ name := "%62" }] ←
                      (Option.get! (State.felts st { name := "%60" }) +
                          Option.get! (State.felts st { name := "%58" })) *
                        Option.get! (State.felts st { name := "%15" }))["%63"] ←ₛ
                    getImpl st { name := "data" } (0 : Back) (14 : ℕ))
                  { name := "%63" }) *
              Option.get! (State.felts st { name := "%19" })) 

def part28_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%15"⟩) ⟨"%60"⟩) ⟨"%58"⟩) ⟨"%61"⟩) ⟨"%63"⟩

-- Run the program from part28 onwards by using part28_state rather than Code.part28
def part28_state_update (st: State): State :=
  Γ (part28_drops (part28_state st)) ⟦Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩⟧

-- Prove that substituting part28_state for Code.part28 produces the same result
lemma part28_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part28;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part28_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) = prog
  unfold Code.part28
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part28_state_update part28_drops part28_state
  rfl

lemma part28_updates_opaque {st : State} : 
  Code.getReturn (part27_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part28_state_update (part27_drops (part27_state st))) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part27_state_update, part28_wp]

lemma part28_cumulative_wp {x0 x1 x2 x3: Felt} :
  Code.run (start_state [x0,x1,x2,x3]) = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17] ↔
  Code.getReturn
        (part28_state_update
          ((({
                  buffers :=
                    ((fun x => Map.empty x)[{ name := "in" }] ←ₘ
                        [[some x0, some x1, some x2, some x3]])[{ name := "data" }] ←ₘ
                      [[some (feltBitAnd x3 (6 : Felt) * (1006632961 : Felt)),
                          some (feltBitAnd x3 (96 : Felt) * (1950351361 : Felt)),
                          some (feltBitAnd x2 (96 : Felt) * (1950351361 : Felt)), some (feltBitAnd x2 (3 : Felt)),
                          some (feltBitAnd x2 (12 : Felt) * (1509949441 : Felt)),
                          some (feltBitAnd x1 (48 : Felt) * (1887436801 : Felt)), some (feltBitAnd x1 (3 : Felt)),
                          some (feltBitAnd x1 (12 : Felt) * (1509949441 : Felt)),
                          some (feltBitAnd x3 (8 : Felt) * (1761607681 : Felt)),
                          some (feltBitAnd x3 (16 : Felt) * (1887436801 : Felt)),
                          some (feltBitAnd x3 (128 : Felt) * (1997537281 : Felt)),
                          some (feltBitAnd x2 (16 : Felt) * (1887436801 : Felt)),
                          some (feltBitAnd x2 (128 : Felt) * (1997537281 : Felt)), some (feltBitAnd x3 (1 : Felt)),
                          some (feltBitAnd x1 (128 : Felt) * (1997537281 : Felt)),
                          some (feltBitAnd x1 (64 : Felt) * (1981808641 : Felt)),
                          some (feltBitAnd x0 (128 : Felt) * (1997537281 : Felt)), some (feltBitAnd x0 (127 : Felt))]],
                  bufferWidths := ((fun x => Map.empty x)[{ name := "data" }] ←ₘ (18 : ℕ))[{ name := "in" }] ←ₘ (4 : ℕ),
                  constraints :=
                    [x2 -
                          ((feltBitAnd x2 (128 : Felt) * (1997537281 : Felt) * (8 : Felt) +
                                    feltBitAnd x2 (96 : Felt) * (1950351361 : Felt) * (2 : Felt) +
                                  feltBitAnd x2 (16 : Felt) * (1887436801 : Felt)) *
                                (16 : Felt) +
                              feltBitAnd x2 (12 : Felt) * (1509949441 : Felt) * (4 : Felt) +
                            feltBitAnd x2 (3 : Felt)) =
                        (0 : Felt),
                      x3 -
                          ((feltBitAnd x3 (128 : Felt) * (1997537281 : Felt) * (64 : Felt) +
                                (feltBitAnd x3 (96 : Felt) * (1950351361 : Felt) * (16 : Felt) +
                                      feltBitAnd x3 (16 : Felt) * (1887436801 : Felt) * (8 : Felt) +
                                    feltBitAnd x3 (8 : Felt) * (1761607681 : Felt) * (4 : Felt) +
                                  feltBitAnd x3 (6 : Felt) * (1006632961 : Felt))) *
                              (2 : Felt) +
                            feltBitAnd x3 (1 : Felt)) =
                        (0 : Felt)],
                  cycle := (0 : ℕ),
                  felts :=
                    (((Map.empty[{ name := "%19" }] ←ₘ (128 : Felt))[{ name := "%15" }] ←ₘ
                          (16 : Felt))[{ name := "%21" }] ←ₘ
                        x1)[{ name := "%20" }] ←ₘ
                      x0,
                  isFailed := false, props := Map.empty,
                  vars := [{ name := "in" }, { name := "data" }] }[felts][{ name := "%57" }] ←
                feltBitAnd x1 (12 : Felt) * (1509949441 : Felt) * (4 : Felt))[felts][{ name := "%60" }] ←
              feltBitAnd x1 (64 : Felt) * (1981808641 : Felt) * (4 : Felt))[felts][{ name := "%58" }] ←
            feltBitAnd x1 (48 : Felt) * (1887436801 : Felt))) =
      [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17]  := by
    rewrite [part27_cumulative_wp]
    rewrite [part28_updates_opaque]
    unfold part27_state
    try simplify_get_hack
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part27_drops
    -- 3 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

end Risc0.ComputeDecode.Witness.WP