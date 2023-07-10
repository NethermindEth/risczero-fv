import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart8

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part9 on st
def part9_state (st: State) : State :=
  
        ((((st["%29"] ←ₛ getImpl st { name := "data" } (0 : Back) (3 : ℕ))[felts][{ name := "%41" }] ←
              Option.get! (State.felts st { name := "%40" }) +
                Option.get!
                  (State.felts (st["%29"] ←ₛ getImpl st { name := "data" } (0 : Back) (3 : ℕ))
                    { name := "%29" }))["%9"] ←ₛ
            getImpl st { name := "in" } (0 : Back) (2 : ℕ))[felts][{ name := "%42" }] ←
          Option.get!
              (State.felts
                (((st["%29"] ←ₛ getImpl st { name := "data" } (0 : Back) (3 : ℕ))[felts][{ name := "%41" }] ←
                    Option.get! (State.felts st { name := "%40" }) +
                      Option.get!
                        (State.felts (st["%29"] ←ₛ getImpl st { name := "data" } (0 : Back) (3 : ℕ))
                          { name := "%29" }))["%9"] ←ₛ
                  getImpl st { name := "in" } (0 : Back) (2 : ℕ))
                { name := "%9" }) -
            (Option.get! (State.felts st { name := "%40" }) +
              Option.get!
                (State.felts (st["%29"] ←ₛ getImpl st { name := "data" } (0 : Back) (3 : ℕ))
                  { name := "%29" }))) 

def part9_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%40"⟩) ⟨"%29"⟩) ⟨"%41"⟩) ⟨"%9"⟩

-- Run the program from part9 onwards by using part9_state rather than Code.part9
def part9_state_update (st: State): State :=
  Γ (part9_drops (part9_state st)) ⟦Code.part10;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part11;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;Code.part12;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part13;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩⟧

-- Prove that substituting part9_state for Code.part9 produces the same result
lemma part9_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part9;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;Code.part10;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part11;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;Code.part12;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part13;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩) st) ↔
  Code.getReturn (part9_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;Code.part10;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part11;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;Code.part12;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part13;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩) = prog
  unfold Code.part9
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part9_state_update part9_drops part9_state
  rfl

lemma part9_updates_opaque {st : State} : 
  Code.getReturn (part8_state_update st) ↔
  Code.getReturn (part9_state_update (part8_drops (part8_state st))) := by
  simp [part8_state_update, part9_wp]

lemma part9_cumulative_wp {x0 x1 x2 x3 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17: Felt} :
  Code.run (start_state [x0,x1,x2,x3] ([y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17])) ↔
  Code.getReturn
      (part9_state_update
        ((((({
                    buffers :=
                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                          [[some y0, some y1, some y2, some y3, some y4, some y5, some y6, some y7, some y8, some y9,
                              some y10, some y11, some y12, some y13, some y14, some y15, some y16,
                              some y17]])[{ name := "in" }] ←ₘ
                        [[some x0, some x1, some x2, some x3]],
                    bufferWidths :=
                      ((fun x => Map.empty x)[{ name := "data" }] ←ₘ (18 : ℕ))[{ name := "in" }] ←ₘ (4 : ℕ),
                    constraints := [], cycle := (0 : ℕ), felts := Map.empty, isFailed := false, props := Map.empty,
                    vars := [{ name := "in" }, { name := "data" }] }[props][{ name := "%6" }] ←
                  True)[felts][{ name := "%4" }] ←
                (4 : Felt))[felts][{ name := "%1" }] ←
              (16 : Felt))[props][{ name := "%28" }] ←
            x3 -
                ((y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) * (2 : Felt) + y13) =
              (0 : Felt))[felts][{ name := "%40" }] ←
          (y12 * (8 : Felt) + y2 * (2 : Felt) + y11) * (16 : Felt) + y4 * (4 : Felt)))  := by
    rewrite [part8_cumulative_wp]
    rewrite [part9_updates_opaque]
    unfold part8_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part8_drops
    -- 5 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

end Risc0.ComputeDecode.Constraints.WP