import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.IsZero.Witness.Code
import Risc0.Gadgets.IsZero.Witness.WeakestPresPart1

namespace Risc0.IsZero.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part2 on st
def part2_state (st: State) : State :=
  
          (if
              Option.get! (State.felts st { name := "%0" : FeltVar }) -
                  Option.get! (State.felts st { name := "%2" : FeltVar }) =
                (0 : Felt) then
            st[felts][{ name := "%3" : FeltVar }] ←
              Option.get! (State.felts st { name := "%0" : FeltVar }) -
                Option.get! (State.felts st { name := "%2" : FeltVar })
          else
            withEqZero
              (Option.get! (State.felts st { name := "%1" : FeltVar }) *
                  Option.get!
                    (State.felts
                      ((st[felts][{ name := "%3" : FeltVar }] ←
                          Option.get! (State.felts st { name := "%0" : FeltVar }) -
                            Option.get! (State.felts st { name := "%2" : FeltVar }))["%4"] ←ₛ
                        getImpl st { name := "data" : BufferVar } (0 : Back) (1 : ℕ))
                      { name := "%4" : FeltVar }) -
                Option.get! (State.felts st { name := "%0" : FeltVar }))
              ((((st[felts][{ name := "%3" : FeltVar }] ←
                      Option.get! (State.felts st { name := "%0" : FeltVar }) -
                        Option.get! (State.felts st { name := "%2" : FeltVar }))["%4"] ←ₛ
                    getImpl st { name := "data" : BufferVar } (0 : Back) (1 : ℕ))[felts][{ name := "%5" : FeltVar }] ←
                  Option.get! (State.felts st { name := "%1" : FeltVar }) *
                    Option.get!
                      (State.felts
                        ((st[felts][{ name := "%3" : FeltVar }] ←
                            Option.get! (State.felts st { name := "%0" : FeltVar }) -
                              Option.get! (State.felts st { name := "%2" : FeltVar }))["%4"] ←ₛ
                          getImpl st { name := "data" : BufferVar } (0 : Back) (1 : ℕ))
                        { name := "%4" : FeltVar }))[felts][{ name := "%6" : FeltVar }] ←
                Option.get! (State.felts st { name := "%1" : FeltVar }) *
                    Option.get!
                      (State.felts
                        ((st[felts][{ name := "%3" : FeltVar }] ←
                            Option.get! (State.felts st { name := "%0" : FeltVar }) -
                              Option.get! (State.felts st { name := "%2" : FeltVar }))["%4"] ←ₛ
                          getImpl st { name := "data" : BufferVar } (0 : Back) (1 : ℕ))
                        { name := "%4" : FeltVar }) -
                  Option.get! (State.felts st { name := "%0" : FeltVar }))) 

def part2_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%1"⟩) ⟨"%4"⟩) ⟨"%5"⟩) ⟨"%2"⟩) ⟨"%0"⟩) ⟨"%3"⟩) ⟨"%6"⟩

-- Run the program from part2 onwards by using part2_state rather than Code.part2
def part2_state_update (st: State): State :=
  part2_drops (part2_state st)

-- Prove that substituting part2_state for Code.part2 produces the same result
lemma part2_wp {st : State} {y0 y1 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part2;dropfelt ⟨"%1"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%6"⟩) st) = [y0, y1] ↔
  Code.getReturn (part2_state_update st) = [y0, y1] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%1"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%6"⟩) = prog
  unfold Code.part2
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_dropfelt]
  unfold part2_state_update part2_drops part2_state
  rfl

lemma part2_updates_opaque {st : State} : 
  Code.getReturn (part1_state_update st) = [y0, y1] ↔
  Code.getReturn (part2_state_update (part1_drops (part1_state st))) = [y0, y1] := by
  simp [part1_state_update, part2_wp]

lemma part2_cumulative_wp {x0: Felt} :
  Code.run (start_state [x0]) = [y0,y1] ↔
  Code.getReturn
        (part2_state_update
          ((if (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) then
              {
                  buffers :=
                    (Map.empty[{ name := "in" : BufferVar }] ←ₘ [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                      [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                          some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                  bufferWidths :=
                    ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                      (1 : ℕ),
                  constraints := [], cycle := (0 : ℕ),
                  felts :=
                    (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ x0)[{ name := "%4" : FeltVar }] ←ₘ
                        if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                      if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                  isFailed := false, props := Map.empty,
                  vars :=
                    [{ name := "in" : BufferVar },
                      { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)
            else
              withEqZero x0
                ({
                    buffers :=
                      (Map.empty[{ name := "in" : BufferVar }] ←ₘ [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                        [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                            some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                    bufferWidths :=
                      ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                          (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                        (1 : ℕ),
                    constraints := [], cycle := (0 : ℕ),
                    felts :=
                      (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ x0)[{ name := "%4" : FeltVar }] ←ₘ
                          if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                        if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                    isFailed := false, props := Map.empty,
                    vars :=
                      [{ name := "in" : BufferVar },
                        { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                  if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)))[felts][{ name := "%0" : FeltVar }] ←
            (1 : Felt))) =
      [y0, y1]  := by
    rewrite [part1_cumulative_wp]
    rewrite [part2_updates_opaque]
    unfold part1_state
    try simplify_get_hack
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part1_drops
    -- 0 drops
    -- simp only [State.drop_update_swap, State.drop_update_same]
    -- rewrite [State.dropFelts]
    -- simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 1 set
    rewrite [Map.drop_of_updates]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

lemma closed_form {x0: Felt} :
  Code.run (start_state [x0]) = [y0,y1] ↔
   (match
        Option.get!
          (State.buffers
            (if ((1 : Felt) - if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) then
              ((if x0 = (0 : Felt) → False then
                    {
                        buffers :=
                          ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                              [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                            [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                        bufferWidths :=
                          ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                              (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                            (1 : ℕ),
                        constraints := [], cycle := (0 : ℕ),
                        felts :=
                          (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ x0)[{ name := "%4" : FeltVar }] ←ₘ
                              if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                            if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                        isFailed := false, props := Map.empty,
                        vars :=
                          [{ name := "in" : BufferVar },
                            { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                      if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)
                  else
                    withEqZero x0
                      ({
                          buffers :=
                            ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                              [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                  some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                          bufferWidths :=
                            ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                              (1 : ℕ),
                          constraints := [], cycle := (0 : ℕ),
                          felts :=
                            (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ x0)[{ name := "%4" : FeltVar }] ←ₘ
                                if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                              if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                          isFailed := false, props := Map.empty,
                          vars :=
                            [{ name := "in" : BufferVar },
                              { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                        if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)))[felts][{ name := "%0" : FeltVar }] ←
                  (1 : Felt))[felts][{ name := "%3" : FeltVar }] ←
                (1 : Felt) - if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)
            else
              withEqZero
                ((x0 *
                    match
                      List.get!
                        (List.get!
                          (match
                            State.buffers
                              (if x0 = (0 : Felt) → False then
                                {
                                    buffers :=
                                      ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                          [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                        [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                            some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                    bufferWidths :=
                                      ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                          (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                        (1 : ℕ),
                                    constraints := [], cycle := (0 : ℕ),
                                    felts :=
                                      (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                            x0)[{ name := "%4" : FeltVar }] ←ₘ
                                          if x0 = (0 : Felt) then (1 : Felt)
                                          else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                        if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                    isFailed := false, props := Map.empty,
                                    vars :=
                                      [{ name := "in" : BufferVar },
                                        { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                  if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)
                              else
                                withEqZero x0
                                  ({
                                      buffers :=
                                        ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                            [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                          [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                      bufferWidths :=
                                        ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                            (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                          (1 : ℕ),
                                      constraints := [], cycle := (0 : ℕ),
                                      felts :=
                                        (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                              x0)[{ name := "%4" : FeltVar }] ←ₘ
                                            if x0 = (0 : Felt) then (1 : Felt)
                                            else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                          if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                      isFailed := false, props := Map.empty,
                                      vars :=
                                        [{ name := "in" : BufferVar },
                                          { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                    if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)))
                              { name := "data" : BufferVar } with
                          | some x => x
                          | none =>
                            panicWithPosWithDecl "Init.Data.Option.BasicAux" "Option.get!" (16 : ℕ) (14 : ℕ)
                              "value is none")
                          (Buffer.Idx.time
                            ((if x0 = (0 : Felt) → False then
                                    {
                                        buffers :=
                                          ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                              [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                            [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                                some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                        bufferWidths :=
                                          ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                              (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                            (1 : ℕ),
                                        constraints := [], cycle := (0 : ℕ),
                                        felts :=
                                          (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                                x0)[{ name := "%4" : FeltVar }] ←ₘ
                                              if x0 = (0 : Felt) then (1 : Felt)
                                              else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                            if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                        isFailed := false, props := Map.empty,
                                        vars :=
                                          [{ name := "in" : BufferVar },
                                            { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                      if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)
                                  else
                                    withEqZero x0
                                      ({
                                          buffers :=
                                            ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                                [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                              [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                                  some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                          bufferWidths :=
                                            ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                                (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                              (1 : ℕ),
                                          constraints := [], cycle := (0 : ℕ),
                                          felts :=
                                            (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                                  x0)[{ name := "%4" : FeltVar }] ←ₘ
                                                if x0 = (0 : Felt) then (1 : Felt)
                                                else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                              if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                          isFailed := false, props := Map.empty,
                                          vars :=
                                            [{ name := "in" : BufferVar },
                                              { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                        if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt))).cycle -
                                Back.toNat (0 : Back),
                              (1 : ℕ))))
                        (Buffer.Idx.data
                          ((if x0 = (0 : Felt) → False then
                                  {
                                      buffers :=
                                        ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                            [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                          [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                      bufferWidths :=
                                        ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                            (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                          (1 : ℕ),
                                      constraints := [], cycle := (0 : ℕ),
                                      felts :=
                                        (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                              x0)[{ name := "%4" : FeltVar }] ←ₘ
                                            if x0 = (0 : Felt) then (1 : Felt)
                                            else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                          if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                      isFailed := false, props := Map.empty,
                                      vars :=
                                        [{ name := "in" : BufferVar },
                                          { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                    if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)
                                else
                                  withEqZero x0
                                    ({
                                        buffers :=
                                          ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                              [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                            [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                                some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                        bufferWidths :=
                                          ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                              (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                            (1 : ℕ),
                                        constraints := [], cycle := (0 : ℕ),
                                        felts :=
                                          (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                                x0)[{ name := "%4" : FeltVar }] ←ₘ
                                              if x0 = (0 : Felt) then (1 : Felt)
                                              else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                            if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                        isFailed := false, props := Map.empty,
                                        vars :=
                                          [{ name := "in" : BufferVar },
                                            { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                      if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt))).cycle -
                              Back.toNat (0 : Back),
                            (1 : ℕ))) with
                    | some x => x
                    | none =>
                      panicWithPosWithDecl "Init.Data.Option.BasicAux" "Option.get!" (16 : ℕ) (14 : ℕ)
                        "value is none") -
                  (1 : Felt))
                ((((((if x0 = (0 : Felt) → False then
                            {
                                buffers :=
                                  ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                      [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                    [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                        some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                bufferWidths :=
                                  ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                      (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                    (1 : ℕ),
                                constraints := [], cycle := (0 : ℕ),
                                felts :=
                                  (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                        x0)[{ name := "%4" : FeltVar }] ←ₘ
                                      if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                    if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                isFailed := false, props := Map.empty,
                                vars :=
                                  [{ name := "in" : BufferVar },
                                    { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                              if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)
                          else
                            withEqZero x0
                              ({
                                  buffers :=
                                    ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                        [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                      [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                          some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                  bufferWidths :=
                                    ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                        (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                      (1 : ℕ),
                                  constraints := [], cycle := (0 : ℕ),
                                  felts :=
                                    (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                          x0)[{ name := "%4" : FeltVar }] ←ₘ
                                        if x0 = (0 : Felt) then (1 : Felt)
                                        else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                      if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                  isFailed := false, props := Map.empty,
                                  vars :=
                                    [{ name := "in" : BufferVar },
                                      { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                if x0 = (0 : Felt) then (1 : Felt)
                                else (0 : Felt)))[felts][{ name := "%0" : FeltVar }] ←
                          (1 : Felt))[felts][{ name := "%3" : FeltVar }] ←
                        (1 : Felt) -
                          if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt))[felts][{ name := "%4" : FeltVar }] ←
                      match
                        List.get!
                          (List.get!
                            (match
                              State.buffers
                                (if x0 = (0 : Felt) → False then
                                  {
                                      buffers :=
                                        ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                            [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                          [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                      bufferWidths :=
                                        ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                            (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                          (1 : ℕ),
                                      constraints := [], cycle := (0 : ℕ),
                                      felts :=
                                        (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                              x0)[{ name := "%4" : FeltVar }] ←ₘ
                                            if x0 = (0 : Felt) then (1 : Felt)
                                            else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                          if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                      isFailed := false, props := Map.empty,
                                      vars :=
                                        [{ name := "in" : BufferVar },
                                          { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                    if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)
                                else
                                  withEqZero x0
                                    ({
                                        buffers :=
                                          ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                              [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                            [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                                some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                        bufferWidths :=
                                          ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                              (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                            (1 : ℕ),
                                        constraints := [], cycle := (0 : ℕ),
                                        felts :=
                                          (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                                x0)[{ name := "%4" : FeltVar }] ←ₘ
                                              if x0 = (0 : Felt) then (1 : Felt)
                                              else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                            if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                        isFailed := false, props := Map.empty,
                                        vars :=
                                          [{ name := "in" : BufferVar },
                                            { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                      if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)))
                                { name := "data" : BufferVar } with
                            | some x => x
                            | none =>
                              panicWithPosWithDecl "Init.Data.Option.BasicAux" "Option.get!" (16 : ℕ) (14 : ℕ)
                                "value is none")
                            (Buffer.Idx.time
                              ((if x0 = (0 : Felt) → False then
                                      {
                                          buffers :=
                                            ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                                [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                              [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                                  some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                          bufferWidths :=
                                            ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                                (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                              (1 : ℕ),
                                          constraints := [], cycle := (0 : ℕ),
                                          felts :=
                                            (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                                  x0)[{ name := "%4" : FeltVar }] ←ₘ
                                                if x0 = (0 : Felt) then (1 : Felt)
                                                else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                              if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                          isFailed := false, props := Map.empty,
                                          vars :=
                                            [{ name := "in" : BufferVar },
                                              { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                        if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)
                                    else
                                      withEqZero x0
                                        ({
                                            buffers :=
                                              ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                                  [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                                [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                                    some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                            bufferWidths :=
                                              ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                                  (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                                (1 : ℕ),
                                            constraints := [], cycle := (0 : ℕ),
                                            felts :=
                                              (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                                    x0)[{ name := "%4" : FeltVar }] ←ₘ
                                                  if x0 = (0 : Felt) then (1 : Felt)
                                                  else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                                if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                            isFailed := false, props := Map.empty,
                                            vars :=
                                              [{ name := "in" : BufferVar },
                                                { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                          if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt))).cycle -
                                  Back.toNat (0 : Back),
                                (1 : ℕ))))
                          (Buffer.Idx.data
                            ((if x0 = (0 : Felt) → False then
                                    {
                                        buffers :=
                                          ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                              [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                            [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                                some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                        bufferWidths :=
                                          ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                              (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                            (1 : ℕ),
                                        constraints := [], cycle := (0 : ℕ),
                                        felts :=
                                          (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                                x0)[{ name := "%4" : FeltVar }] ←ₘ
                                              if x0 = (0 : Felt) then (1 : Felt)
                                              else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                            if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                        isFailed := false, props := Map.empty,
                                        vars :=
                                          [{ name := "in" : BufferVar },
                                            { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                      if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)
                                  else
                                    withEqZero x0
                                      ({
                                          buffers :=
                                            ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                                [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                              [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                                  some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                          bufferWidths :=
                                            ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                                (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                              (1 : ℕ),
                                          constraints := [], cycle := (0 : ℕ),
                                          felts :=
                                            (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                                  x0)[{ name := "%4" : FeltVar }] ←ₘ
                                                if x0 = (0 : Felt) then (1 : Felt)
                                                else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                              if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                          isFailed := false, props := Map.empty,
                                          vars :=
                                            [{ name := "in" : BufferVar },
                                              { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                        if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt))).cycle -
                                Back.toNat (0 : Back),
                              (1 : ℕ))) with
                      | some x => x
                      | none =>
                        panicWithPosWithDecl "Init.Data.Option.BasicAux" "Option.get!" (16 : ℕ) (14 : ℕ)
                          "value is none")[felts][{ name := "%5" : FeltVar }] ←
                    x0 *
                      match
                        List.get!
                          (List.get!
                            (match
                              State.buffers
                                (if x0 = (0 : Felt) → False then
                                  {
                                      buffers :=
                                        ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                            [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                          [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                      bufferWidths :=
                                        ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                            (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                          (1 : ℕ),
                                      constraints := [], cycle := (0 : ℕ),
                                      felts :=
                                        (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                              x0)[{ name := "%4" : FeltVar }] ←ₘ
                                            if x0 = (0 : Felt) then (1 : Felt)
                                            else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                          if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                      isFailed := false, props := Map.empty,
                                      vars :=
                                        [{ name := "in" : BufferVar },
                                          { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                    if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)
                                else
                                  withEqZero x0
                                    ({
                                        buffers :=
                                          ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                              [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                            [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                                some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                        bufferWidths :=
                                          ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                              (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                            (1 : ℕ),
                                        constraints := [], cycle := (0 : ℕ),
                                        felts :=
                                          (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                                x0)[{ name := "%4" : FeltVar }] ←ₘ
                                              if x0 = (0 : Felt) then (1 : Felt)
                                              else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                            if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                        isFailed := false, props := Map.empty,
                                        vars :=
                                          [{ name := "in" : BufferVar },
                                            { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                      if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)))
                                { name := "data" : BufferVar } with
                            | some x => x
                            | none =>
                              panicWithPosWithDecl "Init.Data.Option.BasicAux" "Option.get!" (16 : ℕ) (14 : ℕ)
                                "value is none")
                            (Buffer.Idx.time
                              ((if x0 = (0 : Felt) → False then
                                      {
                                          buffers :=
                                            ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                                [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                              [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                                  some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                          bufferWidths :=
                                            ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                                (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                              (1 : ℕ),
                                          constraints := [], cycle := (0 : ℕ),
                                          felts :=
                                            (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                                  x0)[{ name := "%4" : FeltVar }] ←ₘ
                                                if x0 = (0 : Felt) then (1 : Felt)
                                                else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                              if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                          isFailed := false, props := Map.empty,
                                          vars :=
                                            [{ name := "in" : BufferVar },
                                              { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                        if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)
                                    else
                                      withEqZero x0
                                        ({
                                            buffers :=
                                              ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                                  [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                                [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                                    some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                            bufferWidths :=
                                              ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                                  (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                                (1 : ℕ),
                                            constraints := [], cycle := (0 : ℕ),
                                            felts :=
                                              (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                                    x0)[{ name := "%4" : FeltVar }] ←ₘ
                                                  if x0 = (0 : Felt) then (1 : Felt)
                                                  else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                                if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                            isFailed := false, props := Map.empty,
                                            vars :=
                                              [{ name := "in" : BufferVar },
                                                { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                          if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt))).cycle -
                                  Back.toNat (0 : Back),
                                (1 : ℕ))))
                          (Buffer.Idx.data
                            ((if x0 = (0 : Felt) → False then
                                    {
                                        buffers :=
                                          ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                              [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                            [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                                some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                        bufferWidths :=
                                          ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                              (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                            (1 : ℕ),
                                        constraints := [], cycle := (0 : ℕ),
                                        felts :=
                                          (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                                x0)[{ name := "%4" : FeltVar }] ←ₘ
                                              if x0 = (0 : Felt) then (1 : Felt)
                                              else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                            if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                        isFailed := false, props := Map.empty,
                                        vars :=
                                          [{ name := "in" : BufferVar },
                                            { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                      if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)
                                  else
                                    withEqZero x0
                                      ({
                                          buffers :=
                                            ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                                [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                              [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                                  some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                          bufferWidths :=
                                            ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                                (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                              (1 : ℕ),
                                          constraints := [], cycle := (0 : ℕ),
                                          felts :=
                                            (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                                  x0)[{ name := "%4" : FeltVar }] ←ₘ
                                                if x0 = (0 : Felt) then (1 : Felt)
                                                else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                              if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                          isFailed := false, props := Map.empty,
                                          vars :=
                                            [{ name := "in" : BufferVar },
                                              { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                        if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt))).cycle -
                                Back.toNat (0 : Back),
                              (1 : ℕ))) with
                      | some x => x
                      | none =>
                        panicWithPosWithDecl "Init.Data.Option.BasicAux" "Option.get!" (16 : ℕ) (14 : ℕ)
                          "value is none")[felts][{ name := "%6" : FeltVar }] ←
                  (x0 *
                      match
                        List.get!
                          (List.get!
                            (match
                              State.buffers
                                (if x0 = (0 : Felt) → False then
                                  {
                                      buffers :=
                                        ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                            [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                          [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                              some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                      bufferWidths :=
                                        ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                            (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                          (1 : ℕ),
                                      constraints := [], cycle := (0 : ℕ),
                                      felts :=
                                        (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                              x0)[{ name := "%4" : FeltVar }] ←ₘ
                                            if x0 = (0 : Felt) then (1 : Felt)
                                            else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                          if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                      isFailed := false, props := Map.empty,
                                      vars :=
                                        [{ name := "in" : BufferVar },
                                          { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                    if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)
                                else
                                  withEqZero x0
                                    ({
                                        buffers :=
                                          ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                              [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                            [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                                some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                        bufferWidths :=
                                          ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                              (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                            (1 : ℕ),
                                        constraints := [], cycle := (0 : ℕ),
                                        felts :=
                                          (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                                x0)[{ name := "%4" : FeltVar }] ←ₘ
                                              if x0 = (0 : Felt) then (1 : Felt)
                                              else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                            if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                        isFailed := false, props := Map.empty,
                                        vars :=
                                          [{ name := "in" : BufferVar },
                                            { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                      if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)))
                                { name := "data" : BufferVar } with
                            | some x => x
                            | none =>
                              panicWithPosWithDecl "Init.Data.Option.BasicAux" "Option.get!" (16 : ℕ) (14 : ℕ)
                                "value is none")
                            (Buffer.Idx.time
                              ((if x0 = (0 : Felt) → False then
                                      {
                                          buffers :=
                                            ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                                [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                              [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                                  some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                          bufferWidths :=
                                            ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                                (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                              (1 : ℕ),
                                          constraints := [], cycle := (0 : ℕ),
                                          felts :=
                                            (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                                  x0)[{ name := "%4" : FeltVar }] ←ₘ
                                                if x0 = (0 : Felt) then (1 : Felt)
                                                else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                              if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                          isFailed := false, props := Map.empty,
                                          vars :=
                                            [{ name := "in" : BufferVar },
                                              { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                        if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)
                                    else
                                      withEqZero x0
                                        ({
                                            buffers :=
                                              ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                                  [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                                [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                                    some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                            bufferWidths :=
                                              ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                                  (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                                (1 : ℕ),
                                            constraints := [], cycle := (0 : ℕ),
                                            felts :=
                                              (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                                    x0)[{ name := "%4" : FeltVar }] ←ₘ
                                                  if x0 = (0 : Felt) then (1 : Felt)
                                                  else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                                if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                            isFailed := false, props := Map.empty,
                                            vars :=
                                              [{ name := "in" : BufferVar },
                                                { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                          if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt))).cycle -
                                  Back.toNat (0 : Back),
                                (1 : ℕ))))
                          (Buffer.Idx.data
                            ((if x0 = (0 : Felt) → False then
                                    {
                                        buffers :=
                                          ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                              [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                            [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                                some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                        bufferWidths :=
                                          ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                              (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                            (1 : ℕ),
                                        constraints := [], cycle := (0 : ℕ),
                                        felts :=
                                          (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                                x0)[{ name := "%4" : FeltVar }] ←ₘ
                                              if x0 = (0 : Felt) then (1 : Felt)
                                              else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                            if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                        isFailed := false, props := Map.empty,
                                        vars :=
                                          [{ name := "in" : BufferVar },
                                            { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                      if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)
                                  else
                                    withEqZero x0
                                      ({
                                          buffers :=
                                            ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                                                [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                                              [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                                                  some (if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹)]],
                                          bufferWidths :=
                                            ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                                                (2 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                                              (1 : ℕ),
                                          constraints := [], cycle := (0 : ℕ),
                                          felts :=
                                            (((fun x => Map.empty x)[{ name := "%1" : FeltVar }] ←ₘ
                                                  x0)[{ name := "%4" : FeltVar }] ←ₘ
                                                if x0 = (0 : Felt) then (1 : Felt)
                                                else (0 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                                              if x0 = (0 : Felt) then (0 : Felt) else x0⁻¹,
                                          isFailed := false, props := Map.empty,
                                          vars :=
                                            [{ name := "in" : BufferVar },
                                              { name := "data" : BufferVar }] }[felts][{ name := "%2" : FeltVar }] ←
                                        if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt))).cycle -
                                Back.toNat (0 : Back),
                              (1 : ℕ))) with
                      | some x => x
                      | none =>
                        panicWithPosWithDecl "Init.Data.Option.BasicAux" "Option.get!" (16 : ℕ) (14 : ℕ)
                          "value is none") -
                    (1 : Felt)))
            { name := "data" : BufferVar }) with
      | [] => panicWithPosWithDecl "Init.Data.List.BasicAux" "List.getLast!" (63 : ℕ) (13 : ℕ) "empty list"
      | a :: as => List.getLast (a :: as) (_ : a :: as = [] → List.noConfusionType False (a :: as) []) =
      [y0, y1]  := by
    rewrite [part2_cumulative_wp]
    unfold part2_state_update
    unfold part2_state
    try simplify_get_hack
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part2_drops
    -- 7 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    unfold Code.getReturn
    simp only
    simp [Map.update_get_wobbly, List.getLast!]
end Risc0.IsZero.Witness.WP