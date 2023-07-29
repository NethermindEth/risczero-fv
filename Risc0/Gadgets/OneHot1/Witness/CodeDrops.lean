import Risc0.Gadgets.OneHot1.Witness.CodeParts

namespace Risc0.OneHot1.Witness.Code

open MLIRNotation

lemma drop_past_part1 (h0: ⟨"%1"⟩ ≠ x) (h1: ⟨"%2"⟩ ≠ x) (h2: ⟨"%3"⟩ ≠ x) (h3: ⟨"%0"⟩ ≠ x) (h4: ⟨"%4"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part1; rest⟧) =
  (Γ st ⟦part1; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part1; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part1; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part1
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_sub (by trivial) (by trivial) (by trivial),drop_past_eqz (by trivial),drop_past_const (by trivial),drop_past_get (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part1
    simp only [MLIR.run_seq_def]; try rfl
lemma drop_past_part2 (h0: ⟨"%0"⟩ ≠ x) (h1: ⟨"%4"⟩ ≠ x) (h2: ⟨"%5"⟩ ≠ x) (h3: ⟨"%6"⟩ ≠ x) (h4: ⟨"%7"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part2; rest⟧) =
  (Γ st ⟦part2; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part2; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part2; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part2
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_sub (by trivial) (by trivial) (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_eqz (by trivial),drop_past_sub (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part2
    simp only [MLIR.run_seq_def]; try rfl
lemma drop_past_part3 (h0: ⟨"%7"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part3; rest⟧) =
  (Γ st ⟦part3; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part3; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part3; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part3
    rewrite [drop_sequencing_d]
    rewrite[drop_past_eqz (by trivial)]
    rewrite [←drop_sequencing_d]
    rewrite [h_rhs]
    unfold part3
    simp only [MLIR.run_seq_def]; try rfl

lemma behaviour_with_drops3 :
  Γ st ⟦dropfelt ⟨"%8"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%6"⟩;part3;dropfelt ⟨"%7"⟩⟧ =
  Γ st ⟦part3;dropfelt ⟨"%8"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩⟧ := by
    rewrite [MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part3 (by trivial), ←MLIR.run_seq_def,drop_past_part3 (by trivial), ←MLIR.run_seq_def,drop_past_part3 (by trivial), ←MLIR.run_seq_def,drop_past_part3 (by trivial), ←MLIR.run_seq_def,drop_past_part3 (by trivial), ←MLIR.run_seq_def,drop_past_part3 (by trivial), ←MLIR.run_seq_def,drop_past_part3 (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part3 (by trivial), MLIR.run_seq_def]
    rewrite [←MLIR.run_seq_def]
    simp only [MLIR.run_seq_def]; try rfl
lemma behaviour_with_drops2 :
  Γ st ⟦dropfelt ⟨"%8"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%3"⟩;part2;dropfelt ⟨"%0"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%6"⟩;part3;dropfelt ⟨"%7"⟩⟧ =
  Γ st ⟦part2;part3;dropfelt ⟨"%8"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩⟧ := by
    rewrite [MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part2 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def,drop_past_part2 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def,drop_past_part2 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part2 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), MLIR.run_seq_def]
    rewrite [behaviour_with_drops3, ←MLIR.run_seq_def]
    simp only [MLIR.run_seq_def]; try rfl
lemma behaviour_with_drops1 :
  Γ st ⟦dropfelt ⟨"%8"⟩;part1;dropfelt ⟨"%2"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%3"⟩;part2;dropfelt ⟨"%0"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%6"⟩;part3;dropfelt ⟨"%7"⟩⟧ =
  Γ st ⟦part1;part2;part3;dropfelt ⟨"%8"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩⟧ := by
    rewrite [drop_past_part1 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), MLIR.run_seq_def]
    rewrite [behaviour_with_drops2, ←MLIR.run_seq_def]
    simp only [MLIR.run_seq_def]; try rfl
lemma behaviour_with_drops :
  Γ st ⟦part0;dropfelt ⟨"%8"⟩;part1;dropfelt ⟨"%2"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%3"⟩;part2;dropfelt ⟨"%0"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%6"⟩;part3;dropfelt ⟨"%7"⟩⟧ =
  Γ st ⟦part0;part1;part2;part3;dropfelt ⟨"%8"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩⟧ := by
    rewrite [MLIR.run_seq_def]
    rewrite [behaviour_with_drops1, ←MLIR.run_seq_def]
    simp only [MLIR.run_seq_def]; try rfl
lemma getReturn_ignores_drops :
  getReturn (Γ st ⟦part0;part1;part2;part3;dropfelt ⟨"%8"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩⟧) =
  getReturn (Γ st ⟦part0;part1;part2;part3⟧) := by
    simp [getReturn, MLIR.run_seq_def, State.constraintsInVar, MLIR.run_dropfelt, State.dropFelts_buffers, State.dropFelts_props]

end Risc0.OneHot1.Witness.Code