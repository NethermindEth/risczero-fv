import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart50

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part51 on st
def part51_state (st: State) : State :=
  
          ((withEqZero
              (Option.get! (State.felts st { name := "%67" }) *
                (Option.get! (State.felts st { name := "%18" }) - Option.get! (State.felts st { name := "%67" })))
              ((st[felts][{ name := "%128" }] ←
                  Option.get! (State.felts st { name := "%18" }) -
                    Option.get! (State.felts st { name := "%67" }))[felts][{ name := "%129" }] ←
                Option.get! (State.felts st { name := "%67" }) *
                  (Option.get! (State.felts st { name := "%18" }) -
                    Option.get! (State.felts st { name := "%67" }))))[felts][{ name := "%130" }] ←
            Option.get! (State.felts st { name := "%127" }) + Option.get! (State.felts st { name := "%67" })) 

def part51_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%67"⟩) ⟨"%127"⟩) ⟨"%128"⟩) ⟨"%129"⟩

-- Run the program from part51 onwards by using part51_state rather than Code.part51
def part51_state_update (st: State): State :=
  Γ (part51_drops (part51_state st)) ⟦Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩⟧

-- Prove that substituting part51_state for Code.part51 produces the same result
lemma part51_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part51_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) = prog
  unfold Code.part51
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part51_state_update part51_drops part51_state
  rfl

lemma part51_updates_opaque {st : State} : 
  Code.getReturn (part50_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part51_state_update (part50_drops (part50_state st))) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part50_state_update, part51_wp]

lemma part51_cumulative_wp {x0: Felt} :
  Code.run (start_state [x0]) = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19] ↔
  Code.getReturn
        (part51_state_update
          ({
              buffers :=
                ((fun x => Map.empty x)[{ name := "code" }] ←ₘ [[some x0]])[{ name := "data" }] ←ₘ
                  [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (2 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (3 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (4 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (5 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (6 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (7 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (8 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (9 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (11 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (12 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (13 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (14 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (15 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (16 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (17 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (18 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (19 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))]],
              bufferWidths := ((fun x => Map.empty x)[{ name := "data" }] ←ₘ (20 : ℕ))[{ name := "code" }] ←ₘ (1 : ℕ),
              constraints :=
                [(if x0 - (16 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                    ((1 : Felt) - if x0 - (16 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (if x0 - (15 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                    ((1 : Felt) - if x0 - (15 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (if x0 - (14 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                    ((1 : Felt) - if x0 - (14 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (if x0 - (13 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                    ((1 : Felt) - if x0 - (13 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (if x0 - (12 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                    ((1 : Felt) - if x0 - (12 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (if x0 - (11 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                    ((1 : Felt) - if x0 - (11 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (if x0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                    ((1 : Felt) - if x0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (if x0 - (9 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                    ((1 : Felt) - if x0 - (9 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (if x0 - (8 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                    ((1 : Felt) - if x0 - (8 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (if x0 - (7 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                    ((1 : Felt) - if x0 - (7 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (if x0 - (6 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                    ((1 : Felt) - if x0 - (6 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (if x0 - (5 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                    ((1 : Felt) - if x0 - (5 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (if x0 - (4 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                    ((1 : Felt) - if x0 - (4 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (if x0 - (3 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                    ((1 : Felt) - if x0 - (3 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (if x0 - (2 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                    ((1 : Felt) - if x0 - (2 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (if x0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                    ((1 : Felt) - if x0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                    ((1 : Felt) - if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (if x0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                                          (if x0 - (2 : Felt) = (0 : Felt) then (1 : Felt)
                                                            else (0 : Felt)) *
                                                            (2 : Felt) +
                                                        (if x0 - (3 : Felt) = (0 : Felt) then (1 : Felt)
                                                          else (0 : Felt)) *
                                                          (3 : Felt) +
                                                      (if x0 - (4 : Felt) = (0 : Felt) then (1 : Felt)
                                                        else (0 : Felt)) *
                                                        (4 : Felt) +
                                                    (if x0 - (5 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) *
                                                      (5 : Felt) +
                                                  (if x0 - (6 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) *
                                                    (6 : Felt) +
                                                (if x0 - (7 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) *
                                                  (7 : Felt) +
                                              (if x0 - (8 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) *
                                                (8 : Felt) +
                                            (if x0 - (9 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) *
                                              (9 : Felt) +
                                          (if x0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) *
                                            (10 : Felt) +
                                        (if x0 - (11 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) *
                                          (11 : Felt) +
                                      (if x0 - (12 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (12 : Felt) +
                                    (if x0 - (13 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (13 : Felt) +
                                  (if x0 - (14 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (14 : Felt) +
                                (if x0 - (15 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (15 : Felt) +
                              (if x0 - (16 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (16 : Felt) +
                            (if x0 - (17 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (17 : Felt) +
                          (if x0 - (18 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (18 : Felt) +
                        (if x0 - (19 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (19 : Felt) -
                      x0 =
                    (0 : Felt)],
              cycle := (0 : ℕ),
              felts :=
                (((Map.empty[{ name := "%18" }] ←ₘ (1 : Felt))[{ name := "%67" }] ←ₘ
                      if x0 - (17 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))[{ name := "%70" }] ←ₘ
                    if x0 - (18 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))[{ name := "%73" }] ←ₘ
                  if x0 - (19 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt),
              isFailed := false, props := Map.empty,
              vars := [{ name := "code" }, { name := "data" }] }[felts][{ name := "%127" }] ←
            ((((((((((((((((if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                            if x0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                          if x0 - (2 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                        if x0 - (3 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                      if x0 - (4 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                    if x0 - (5 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                  if x0 - (6 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                if x0 - (7 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                              if x0 - (8 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                            if x0 - (9 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                          if x0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                        if x0 - (11 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                      if x0 - (12 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                    if x0 - (13 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                  if x0 - (14 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                if x0 - (15 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
              if x0 - (16 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))) =
      [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19]  := by
    rewrite [part50_cumulative_wp]
    rewrite [part51_updates_opaque]
    unfold part50_state
    try simplify_get_hack
    MLIR_states_updates
    -- 1 withEqZero
    rewrite [withEqZero_def]
    MLIR_states_updates
    unfold part50_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

end Risc0.OneHot20.Witness.WP