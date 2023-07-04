import Risc0.Gadgets.OneHot2.Witness.CodeParts

namespace Risc0.OneHot2.Witness.Code

open MLIRNotation

lemma drop_past_part1 (h0: ⟨"%2"⟩ ≠ x) (h1: ⟨"%0"⟩ ≠ x) (h2: ⟨"%13"⟩ ≠ x) (h3: ⟨"%14"⟩ ≠ x) (h4: ⟨"%3"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part1; rest⟧) =
  (Γ st ⟦part1; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part1; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part1; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part1
    rewrite [drop_sequencing_nnnd]
    rewrite[drop_past_sub (by trivial) (by trivial) (by trivial),drop_past_isz (by trivial) (by trivial),drop_past_set (by trivial),drop_past_get (by trivial)]
    rewrite [←drop_sequencing_nnnd]
    rewrite [h_rhs]
    unfold part1
    rfl
lemma drop_past_part2 (h0: ⟨"%3"⟩ ≠ x) (h1: ⟨"%2"⟩ ≠ x) (h2: ⟨"%4"⟩ ≠ x) (h3: ⟨"%5"⟩ ≠ x) (h4: ⟨"%0"⟩ ≠ x) (h5: ⟨"%6"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part2; rest⟧) =
  (Γ st ⟦part2; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part2; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part2; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part2
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_sub (by trivial) (by trivial) (by trivial),drop_past_eqz (by trivial),drop_past_get (by trivial),drop_past_sub (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part2
    rfl
lemma drop_past_part3 (h0: ⟨"%5"⟩ ≠ x) (h1: ⟨"%6"⟩ ≠ x) (h2: ⟨"%7"⟩ ≠ x) (h3: ⟨"%0"⟩ ≠ x) (h4: ⟨"%3"⟩ ≠ x) (h5: ⟨"%8"⟩ ≠ x) (h6: ⟨"%9"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part3; rest⟧) =
  (Γ st ⟦part3; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part3; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part3; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part3
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_eqz (by trivial),drop_past_sub (by trivial) (by trivial) (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part3
    rfl
lemma drop_past_part4 (h0: ⟨"%9"⟩ ≠ x) (h1: ⟨"%5"⟩ ≠ x) (h2: ⟨"%3"⟩ ≠ x) (h3: ⟨"%10"⟩ ≠ x) (h4: ⟨"%0"⟩ ≠ x) (h5: ⟨"%11"⟩ ≠ x) (h6: ⟨"%1"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part4; rest⟧) =
  (Γ st ⟦part4; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part4; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part4; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part4
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_eqz (by trivial),drop_past_add (by trivial) (by trivial) (by trivial),drop_past_sub (by trivial) (by trivial) (by trivial),drop_past_const (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part4
    rfl
lemma drop_past_part5 (h0: ⟨"%11"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part5; rest⟧) =
  (Γ st ⟦part5; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part5; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part5; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part5
    rewrite [drop_sequencing_d]
    rewrite[drop_past_eqz (by trivial)]
    rewrite [←drop_sequencing_d]
    rewrite [h_rhs]
    unfold part5
    rfl

lemma behaviour_with_drops5_1 :
  Γ st ⟦dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;part5;rest⟧ =
  Γ st ⟦part5;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;rest⟧ := by
    rewrite [MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial), ←MLIR.run_seq_def,drop_past_part5 (by trivial), ←MLIR.run_seq_def,drop_past_part5 (by trivial), ←MLIR.run_seq_def,drop_past_part5 (by trivial), ←MLIR.run_seq_def,drop_past_part5 (by trivial), ←MLIR.run_seq_def,drop_past_part5 (by trivial), ←MLIR.run_seq_def,drop_past_part5 (by trivial), ←MLIR.run_seq_def,drop_past_part5 (by trivial), ←MLIR.run_seq_def,drop_past_part5 (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part5 (by trivial)]
lemma behaviour_with_drops5 :
  Γ st ⟦dropfelt ⟨"%12"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧ =
  Γ st ⟦part5;dropfelt ⟨"%12"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧ := by
    rewrite [MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [behaviour_with_drops5_1, ←MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial), ←MLIR.run_seq_def,drop_past_part5 (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial), MLIR.run_seq_def]
    rewrite [←MLIR.run_seq_def]
    rfl
lemma behaviour_with_drops4 :
  Γ st ⟦dropfelt ⟨"%12"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧ =
  Γ st ⟦part4;part5;dropfelt ⟨"%12"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧ := by
    rewrite [MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def,drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def,drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def,drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def,drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def,drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def,drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), MLIR.run_seq_def]
    rewrite [behaviour_with_drops5, ←MLIR.run_seq_def]
    rfl
lemma behaviour_with_drops3 :
  Γ st ⟦dropfelt ⟨"%12"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;part3;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧ =
  Γ st ⟦part3;part4;part5;dropfelt ⟨"%12"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧ := by
    rewrite [MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part3 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def,drop_past_part3 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def,drop_past_part3 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def,drop_past_part3 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part3 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), MLIR.run_seq_def]
    rewrite [behaviour_with_drops4, ←MLIR.run_seq_def]
    rfl
lemma behaviour_with_drops2 :
  Γ st ⟦dropfelt ⟨"%12"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;part3;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧ =
  Γ st ⟦part2;part3;part4;part5;dropfelt ⟨"%12"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧ := by
    rewrite [MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part2 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def,drop_past_part2 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part2 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), MLIR.run_seq_def]
    rewrite [behaviour_with_drops3, ←MLIR.run_seq_def]
    rfl
lemma behaviour_with_drops1 :
  Γ st ⟦dropfelt ⟨"%12"⟩;part1;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;part3;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧ =
  Γ st ⟦part1;part2;part3;part4;part5;dropfelt ⟨"%12"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧ := by
    rewrite [drop_past_part1 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), MLIR.run_seq_def]
    rewrite [behaviour_with_drops2, ←MLIR.run_seq_def]
    rfl
lemma behaviour_with_drops :
  Γ st ⟦part0;dropfelt ⟨"%12"⟩;part1;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;part3;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧ =
  Γ st ⟦part0;part1;part2;part3;part4;part5;dropfelt ⟨"%12"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧ := by
    rewrite [MLIR.run_seq_def]
    rewrite [behaviour_with_drops1, ←MLIR.run_seq_def]
    rfl
lemma getReturn_ignores_drops :
  getReturn (Γ st ⟦part0;part1;part2;part3;part4;part5;dropfelt ⟨"%12"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧) =
  getReturn (Γ st ⟦part0;part1;part2;part3;part4;part5⟧) := by
    simp [getReturn, MLIR.run_seq_def, State.constraintsInVar, MLIR.run_dropfelt, State.dropFelts_buffers, State.dropFelts_props]

end Risc0.OneHot2.Witness.Code