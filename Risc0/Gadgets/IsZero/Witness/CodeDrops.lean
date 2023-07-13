import Risc0.Gadgets.IsZero.Witness.CodeParts

namespace Risc0.IsZero.Witness.Code

open MLIRNotation

lemma drop_past_part1 (h0: ⟨"%5"⟩ ≠ x) (h1: ⟨"%2"⟩ ≠ x) (h2: ⟨"%1"⟩ ≠ x) (h3: ⟨"%0"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part1; rest⟧) =
  (Γ st ⟦part1; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part1; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part1; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part1
    rewrite [drop_sequencing_nddd]
    rewrite[drop_past_set (by trivial),drop_past_get (by trivial),drop_past_if (by trivial) (drop_past_eqz  (by trivial)),drop_past_const (by trivial)]
    rewrite [←drop_sequencing_nddd]
    rewrite [h_rhs]
    unfold part1
    rfl
lemma drop_past_part2 (h0: ⟨"%0"⟩ ≠ x) (h1: ⟨"%2"⟩ ≠ x) (h2: ⟨"%3"⟩ ≠ x) (h3: ⟨"%1"⟩ ≠ x) (h4: ⟨"%4"⟩ ≠ x) (h5: ⟨"%5"⟩ ≠ x) (h6: ⟨"%6"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part2; rest⟧) =
  (Γ st ⟦part2; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part2; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part2; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part2
    rewrite [drop_sequencing_dd]
    rewrite[drop_past_sub (by trivial) (by trivial) (by trivial),drop_past_if (by trivial) (opt_seq (drop_past_get  (by trivial)) (opt_seq (drop_past_mul  (by trivial) (by trivial) (by trivial)) (opt_seq (drop_past_sub  (by trivial) (by trivial) (by trivial)) (drop_past_eqz  (by trivial)))))]
    rewrite [←drop_sequencing_dd]
    rewrite [h_rhs]
    unfold part2
    rfl

lemma behaviour_with_drops2 :
  Γ st ⟦part2;dropfelt ⟨"%1"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%6"⟩⟧ =
  Γ st ⟦part2;dropfelt ⟨"%1"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%6"⟩⟧ := by
    rewrite [MLIR.run_seq_def]
    rewrite [←MLIR.run_seq_def]
    rfl
lemma behaviour_with_drops1 :
  Γ st ⟦part1;part2;dropfelt ⟨"%1"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%6"⟩⟧ =
  Γ st ⟦part1;part2;dropfelt ⟨"%1"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%6"⟩⟧ := by
    rewrite [MLIR.run_seq_def]
    rewrite [behaviour_with_drops2, ←MLIR.run_seq_def]
    rfl
lemma behaviour_with_drops :
  Γ st ⟦part0;part1;part2;dropfelt ⟨"%1"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%6"⟩⟧ =
  Γ st ⟦part0;part1;part2;dropfelt ⟨"%1"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%6"⟩⟧ := by
    rewrite [MLIR.run_seq_def]
    rewrite [behaviour_with_drops1, ←MLIR.run_seq_def]
    rfl
lemma getReturn_ignores_drops :
  getReturn (Γ st ⟦part0;part1;part2;dropfelt ⟨"%1"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%6"⟩⟧) =
  getReturn (Γ st ⟦part0;part1;part2⟧) := by
    simp [getReturn, MLIR.run_seq_def, State.constraintsInVar, MLIR.run_dropfelt, State.dropFelts_buffers, State.dropFelts_props]

end Risc0.IsZero.Witness.Code