import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.IsZero.Constraints.CodeDrops

namespace Risc0.IsZero.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part0 on st
def part0_state (st: State) : State :=
  if Γ st ⟦Code.part0⟧.isFailed = true
  then {st with isFailed := true}
  else ((((st[props][{ name := "%1" : PropVar }] ← True)[felts][{ name := "%2" : FeltVar }] ←
          Option.get!
            (Buffer.back st { name := "in" : BufferVar } (0 : Back) (0 : ℕ)))[props][{ name := "%4" : PropVar }] ←
        Option.get! (Buffer.back st { name := "in" : BufferVar } (0 : Back) (0 : ℕ)) =
          (0 : Felt))[felts][{ name := "%3" : FeltVar }] ←
      Option.get! (Buffer.back st { name := "data" : BufferVar } (0 : Back) (0 : ℕ)))

def part0_drops (st: State) : State :=
  st

-- Run the whole program by using part0_state rather than Code.part0
def part0_state_update (st: State): State :=
  Γ (part0_drops (part0_state st)) ⟦Code.part1;dropfelt ⟨"%3"⟩;Code.part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%9"⟩⟧

-- Prove that substituting part0_state for Code.part0 produces the same result
lemma part0_wp {st : State} :
  Code.getReturn (Γ st ⟦Code.part0;Code.part1;dropfelt ⟨"%3"⟩;Code.part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%9"⟩⟧)↔
  Code.getReturn (part0_state_update st) := by
  generalize eq : (Code.part1;dropfelt ⟨"%3"⟩;Code.part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%9"⟩) = prog
  rewrite [MLIR.run_seq_def]
  unfold part0_state_update
  rewrite [eq]
  by_cases hIsFailed: (Γ st ⟦Code.part0⟧).isFailed
  . have hFailedFull : (Γ (Γ st ⟦Code.part0⟧) ⟦prog⟧).isFailed = true := by simp [MLIR.isFailed_monotonic, hIsFailed]
    unfold Code.getReturn
    simp [hFailedFull]
    intro
    unfold part0_state part0_drops
    simp [hIsFailed, MLIR.isFailed_monotonic]
  . have h_SameIfValid : (Γ st ⟦Code.part0⟧) = (part0_drops (part0_state st)) := by
      have h_SAVE: ¬Γ st ⟦Code.part0⟧.isFailed = true := hIsFailed --REVIEW another way to duplicate a goal?
      generalize eq_st': Γ st ⟦Code.part0⟧ = st'
      rewrite [eq_st'] at hIsFailed
      unfold Code.part0 at eq_st'
      -- MLIR START --REVIEW how to target our tactics at a hypothesis
      rewrite [MLIR.run_seq_def] at eq_st'
      repeat (
        first
        | rewrite [MLIR.run_ass_def] at eq_st'
        | rewrite [MLIR.run_set_def] at eq_st'
        | rewrite [MLIR.run_if] at eq_st'
        | rewrite [MLIR.run_nondet] at eq_st'
        | rewrite [MLIR.run_eqz] at eq_st'
        | rewrite [MLIR.run_dropfelt] at eq_st'
      )
      -- simp only [
      --   Op.eval_const, Op.eval_true, Op.eval_getBuffer, Op.eval_add, Op.eval_sub,
      --   Op.eval_mul, Op.eval_isz, Op.eval_inv, Op.eval_andEqz, Op.eval_andCond
      -- ] at eq_st'
      rewrite [MLIR.run_seq_def] at eq_st'
      repeat (
        first
        | rewrite [MLIR.run_ass_def] at eq_st'
        | rewrite [MLIR.run_set_def] at eq_st'
        | rewrite [MLIR.run_if] at eq_st'
        | rewrite [MLIR.run_nondet] at eq_st'
        | rewrite [MLIR.run_eqz] at eq_st'
        | rewrite [MLIR.run_dropfelt] at eq_st'
      )
      -- simp only [
      --   Op.eval_const, Op.eval_true, Op.eval_getBuffer, Op.eval_add, Op.eval_sub,
      --   Op.eval_mul, Op.eval_isz, Op.eval_inv, Op.eval_andEqz, Op.eval_andCond
      -- ] at eq_st'
      rewrite [MLIR.run_seq_def] at eq_st'
      repeat (
        first
        | rewrite [MLIR.run_ass_def] at eq_st'
        | rewrite [MLIR.run_set_def] at eq_st'
        | rewrite [MLIR.run_if] at eq_st'
        | rewrite [MLIR.run_nondet] at eq_st'
        | rewrite [MLIR.run_eqz] at eq_st'
        | rewrite [MLIR.run_dropfelt] at eq_st'
      )
      simp only [
        Op.eval_const, Op.eval_true, Op.eval_getBuffer, Op.eval_add, Op.eval_sub,
        Op.eval_mul, Op.eval_isz, Op.eval_inv, Op.eval_andEqz, Op.eval_andCond
      ] at eq_st'
      try simp only [Buffer.back_def.symm, isGetValid_def.symm, getImpl_def.symm, State.update_val', State.update_constr'] at eq_st'
      try simp [getImpl_skip_set_offset] at eq_st'
      --MLIR END

      --SIMPLIFY VALID START (2 gets means 2 rewrites using simplify_valid_get)
      rewrite [←eq_st'] at hIsFailed
      try simp only [State.updateFelts_isFailed, State.updateProps_isFailed] at hIsFailed
      rewrite [simplify_valid_get hIsFailed] at eq_st' hIsFailed
      try simp only [State.updateFelts_isFailed, State.updateProps_isFailed] at hIsFailed
      rewrite [simplify_valid_get hIsFailed] at eq_st' hIsFailed
      --SIMPLIFY VALID END
      rewrite [←eq_st']
      MLIR
      unfold part0_drops part0_state
      simp only [h_SAVE, ite_false]

    rw [h_SameIfValid]

lemma part0_cumulative_wp {x0 y0 y1: Felt}:
  Code.run (start_state [x0] ([y0,y1])) ↔
  Code.getReturn
      (part0_state_update
        {
          buffers :=
            Map.fromList
              [({ name := "in" : BufferVar }, [[some x0]]), ({ name := "data" : BufferVar }, [[some y0, some y1]])],
          bufferWidths :=
            Map.fromList [({ name := "in" : BufferVar }, (1 : ℕ)), ({ name := "data" : BufferVar }, (2 : ℕ))],
          constraints := [], cycle := (0 : ℕ), felts := Map.empty, isFailed := false, props := Map.empty,
          vars := [{ name := "in" : BufferVar }, { name := "data" : BufferVar }] })  := by
    unfold Code.run start_state
    rewrite [Code.optimised_behaviour_full]
    unfold MLIR.runProgram
    rewrite [←Code.parts_combine]
    unfold Code.parts_combined
    rewrite [←Code.getReturn_ignores_drops]
    rewrite [←Code.behaviour_with_drops]
    rewrite [part0_wp]
    rfl

end Risc0.IsZero.Constraints.WP