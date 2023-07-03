import Risc0.Gadgets.ComputeDecode.Constraints.CodeParts

namespace Risc0.ComputeDecode.Constraints.Code

open MLIRNotation

lemma drop_past_part1 (h0: ⟨"%2"⟩ ≠ x) (h1: ⟨"%15"⟩ ≠ x) (h2: ⟨"%16"⟩ ≠ x) (h3: ⟨"%1"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part1; rest⟧) =
  (Γ st ⟦part1; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part1; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part1; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part1
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_const (by trivial),drop_past_get (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_const (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part1
    rfl
lemma drop_past_part2 (h0: ⟨"%17"⟩ ≠ x) (h1: ⟨"%1"⟩ ≠ x) (h2: ⟨"%18"⟩ ≠ x) (h3: ⟨"%16"⟩ ≠ x) (h4: ⟨"%19"⟩ ≠ x) (h5: ⟨"%14"⟩ ≠ x) (h6: ⟨"%20"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part2; rest⟧) =
  (Γ st ⟦part2; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part2; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part2; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part2
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_get (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_add (by trivial) (by trivial) (by trivial),drop_past_add (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part2
    rfl
lemma drop_past_part3 (h0: ⟨"%12"⟩ ≠ x) (h1: ⟨"%20"⟩ ≠ x) (h2: ⟨"%21"⟩ ≠ x) (h3: ⟨"%5"⟩ ≠ x) (h4: ⟨"%22"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part3; rest⟧) =
  (Γ st ⟦part3; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part3; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part3; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part3
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_get (by trivial),drop_past_add (by trivial) (by trivial) (by trivial),drop_past_const (by trivial),drop_past_get (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part3
    rfl
lemma drop_past_part4 (h0: ⟨"%22"⟩ ≠ x) (h1: ⟨"%5"⟩ ≠ x) (h2: ⟨"%23"⟩ ≠ x) (h3: ⟨"%21"⟩ ≠ x) (h4: ⟨"%24"⟩ ≠ x) (h5: ⟨"%3"⟩ ≠ x) (h6: ⟨"%25"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part4; rest⟧) =
  (Γ st ⟦part4; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part4; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part4; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part4
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_add (by trivial) (by trivial) (by trivial),drop_past_const (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part4
    rfl
lemma drop_past_part5 (h0: ⟨"%11"⟩ ≠ x) (h1: ⟨"%25"⟩ ≠ x) (h2: ⟨"%26"⟩ ≠ x) (h3: ⟨"%10"⟩ ≠ x) (h4: ⟨"%27"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part5; rest⟧) =
  (Γ st ⟦part5; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part5; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part5; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part5
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_get (by trivial),drop_past_add (by trivial) (by trivial) (by trivial),drop_past_get (by trivial),drop_past_sub (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part5
    rfl
lemma drop_past_part6 (h0: ⟨"%27"⟩ ≠ x) (h1: ⟨"%28"⟩ ≠ x) (h2: ⟨"%30"⟩ ≠ x) (h3: ⟨"%4"⟩ ≠ x) (h4: ⟨"%31"⟩ ≠ x) (h5: ⟨"%33"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part6; rest⟧) =
  (Γ st ⟦part6; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part6; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part6; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part6
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_andEqz (by trivial) (by trivial),drop_past_get (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_get (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part6
    rfl
lemma drop_past_part7 (h0: ⟨"%33"⟩ ≠ x) (h1: ⟨"%3"⟩ ≠ x) (h2: ⟨"%34"⟩ ≠ x) (h3: ⟨"%35"⟩ ≠ x) (h4: ⟨"%2"⟩ ≠ x) (h5: ⟨"%36"⟩ ≠ x) (h6: ⟨"%37"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part7; rest⟧) =
  (Γ st ⟦part7; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part7; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part7; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part7
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_get (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_add (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part7
    rfl
lemma drop_past_part8 (h0: ⟨"%32"⟩ ≠ x) (h1: ⟨"%37"⟩ ≠ x) (h2: ⟨"%38"⟩ ≠ x) (h3: ⟨"%1"⟩ ≠ x) (h4: ⟨"%39"⟩ ≠ x) (h5: ⟨"%31"⟩ ≠ x) (h6: ⟨"%40"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part8; rest⟧) =
  (Γ st ⟦part8; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part8; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part8; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part8
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_get (by trivial),drop_past_add (by trivial) (by trivial) (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_add (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part8
    rfl
lemma drop_past_part9 (h0: ⟨"%29"⟩ ≠ x) (h1: ⟨"%40"⟩ ≠ x) (h2: ⟨"%41"⟩ ≠ x) (h3: ⟨"%9"⟩ ≠ x) (h4: ⟨"%42"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part9; rest⟧) =
  (Γ st ⟦part9; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part9; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part9; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part9
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_get (by trivial),drop_past_add (by trivial) (by trivial) (by trivial),drop_past_get (by trivial),drop_past_sub (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part9
    rfl
lemma drop_past_part10 (h0: ⟨"%42"⟩ ≠ x) (h1: ⟨"%43"⟩ ≠ x) (h2: ⟨"%45"⟩ ≠ x) (h3: ⟨"%4"⟩ ≠ x) (h4: ⟨"%46"⟩ ≠ x) (h5: ⟨"%48"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part10; rest⟧) =
  (Γ st ⟦part10; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part10; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part10; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part10
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_andEqz (by trivial) (by trivial),drop_past_get (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_get (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part10
    rfl
lemma drop_past_part11 (h0: ⟨"%48"⟩ ≠ x) (h1: ⟨"%4"⟩ ≠ x) (h2: ⟨"%49"⟩ ≠ x) (h3: ⟨"%47"⟩ ≠ x) (h4: ⟨"%50"⟩ ≠ x) (h5: ⟨"%1"⟩ ≠ x) (h6: ⟨"%51"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part11; rest⟧) =
  (Γ st ⟦part11; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part11; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part11; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part11
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_get (by trivial),drop_past_add (by trivial) (by trivial) (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part11
    rfl
lemma drop_past_part12 (h0: ⟨"%0"⟩ ≠ x) (h1: ⟨"%52"⟩ ≠ x) (h2: ⟨"%53"⟩ ≠ x) (h3: ⟨"%51"⟩ ≠ x) (h4: ⟨"%54"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part12; rest⟧) =
  (Γ st ⟦part12; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part12; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part12; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part12
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_const (by trivial),drop_past_get (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_add (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part12
    rfl
lemma drop_past_part13 (h0: ⟨"%54"⟩ ≠ x) (h1: ⟨"%46"⟩ ≠ x) (h2: ⟨"%55"⟩ ≠ x) (h3: ⟨"%44"⟩ ≠ x) (h4: ⟨"%56"⟩ ≠ x) (h5: ⟨"%8"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part13; rest⟧) =
  (Γ st ⟦part13; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part13; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part13; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part13
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_add (by trivial) (by trivial) (by trivial),drop_past_get (by trivial),drop_past_add (by trivial) (by trivial) (by trivial),drop_past_get (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part13
    rfl
lemma drop_past_part14 (h0: ⟨"%8"⟩ ≠ x) (h1: ⟨"%56"⟩ ≠ x) (h2: ⟨"%57"⟩ ≠ x) (h3: ⟨"%58"⟩ ≠ x) (h4: ⟨"%60"⟩ ≠ x) (h5: ⟨"%0"⟩ ≠ x) (h6: ⟨"%61"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part14; rest⟧) =
  (Γ st ⟦part14; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part14; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part14; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part14
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_sub (by trivial) (by trivial) (by trivial),drop_past_andEqz (by trivial) (by trivial),drop_past_get (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part14
    rfl
lemma drop_past_part15 (h0: ⟨"%59"⟩ ≠ x) (h1: ⟨"%61"⟩ ≠ x) (h2: ⟨"%62"⟩ ≠ x) (h3: ⟨"%7"⟩ ≠ x) (h4: ⟨"%63"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part15; rest⟧) =
  (Γ st ⟦part15; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part15; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part15; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part15
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_get (by trivial),drop_past_add (by trivial) (by trivial) (by trivial),drop_past_get (by trivial),drop_past_sub (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part15
    rfl
lemma drop_past_part16 (h0: ⟨"%63"⟩ ≠ x) (h1: ⟨"%64"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part16; rest⟧) =
  (Γ st ⟦part16; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part16; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part16; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part16
    rewrite [drop_sequencing_d]
    rewrite[drop_past_andEqz (by trivial) (by trivial)]
    rewrite [←drop_sequencing_d]
    rewrite [h_rhs]
    unfold part16
    rfl

lemma behaviour_with_drops1 :
  Γ st ⟦dropfelt ⟨"%13"⟩;part1;rest⟧ =
  Γ st ⟦part1;dropfelt ⟨"%13"⟩;rest⟧ := by
    rw [drop_past_part1 (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops2 :
  Γ st ⟦dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;part2;rest⟧ =
  Γ st ⟦part2;dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def]
    rewrite [drop_past_part2 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part2 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops3 :
  Γ st ⟦dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;part3;rest⟧ =
  Γ st ⟦part3;dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part3 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part3 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part3 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part3 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part3 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part3 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part3 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops4 :
  Γ st ⟦dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;part4;rest⟧ =
  Γ st ⟦part4;dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops5 :
  Γ st ⟦dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;part5;rest⟧ =
  Γ st ⟦part5;dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops6 :
  Γ st ⟦dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;part6;rest⟧ =
  Γ st ⟦part6;dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops7 :
  Γ st ⟦dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;part7;rest⟧ =
  Γ st ⟦part7;dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops8 :
  Γ st ⟦dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;part8;rest⟧ =
  Γ st ⟦part8;dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops9 :
  Γ st ⟦dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;part9;rest⟧ =
  Γ st ⟦part9;dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops10 :
  Γ st ⟦dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;part10;rest⟧ =
  Γ st ⟦part10;dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops11 :
  Γ st ⟦dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;part11;rest⟧ =
  Γ st ⟦part11;dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops12 :
  Γ st ⟦dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;part12;rest⟧ =
  Γ st ⟦part12;dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops13 :
  Γ st ⟦dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;part13;rest⟧ =
  Γ st ⟦part13;dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops14 :
  Γ st ⟦dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;part14;rest⟧ =
  Γ st ⟦part14;dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops15 :
  Γ st ⟦dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;part15;rest⟧ =
  Γ st ⟦part15;dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops16 :
  Γ st ⟦dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;part16;rest⟧ =
  Γ st ⟦part16;dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part16 (by trivial) (by trivial)]
lemma behaviour_with_drops :
  Γ st ⟦part0;dropfelt ⟨"%13"⟩;part1;dropfelt ⟨"%15"⟩;part2;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;part3;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;part4;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;part5;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;part6;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;part7;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;part8;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;part9;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;part10;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;part11;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;part12;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;part13;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;part16;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩⟧ =
  Γ st ⟦part0;part1;part2;part3;part4;part5;part6;part7;part8;part9;part10;part11;part12;part13;part14;part15;part16;dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩⟧ := by
    let rhs : State := (Γ st ⟦part0;part1;part2;part3;part4;part5;part6;part7;part8;part9;part10;part11;part12;part13;part14;part15;part16;dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩⟧)
    have h_rhs : rhs = Γ st ⟦part0;part1;part2;part3;part4;part5;part6;part7;part8;part9;part10;part11;part12;part13;part14;part15;part16;dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩⟧ := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def]
    let st0 : State := (Γ st ⟦part0⟧)
    have h_st0 : st0 = (Γ st ⟦part0⟧) := rfl
    rewrite [←h_st0]
    rewrite [behaviour_with_drops1]
    rewrite [MLIR.run_seq_def]
    let st1 : State := (Γ st0 ⟦part1⟧)
    have h_st1 : st1 = (Γ st0 ⟦part1⟧) := rfl
    rewrite [←h_st1]
    rewrite [behaviour_with_drops2]
    rewrite [MLIR.run_seq_def]
    let st2 : State := (Γ st1 ⟦part2⟧)
    have h_st2 : st2 = (Γ st1 ⟦part2⟧) := rfl
    rewrite [←h_st2]
    rewrite [behaviour_with_drops3]
    rewrite [MLIR.run_seq_def]
    let st3 : State := (Γ st2 ⟦part3⟧)
    have h_st3 : st3 = (Γ st2 ⟦part3⟧) := rfl
    rewrite [←h_st3]
    rewrite [behaviour_with_drops4]
    rewrite [MLIR.run_seq_def]
    let st4 : State := (Γ st3 ⟦part4⟧)
    have h_st4 : st4 = (Γ st3 ⟦part4⟧) := rfl
    rewrite [←h_st4]
    rewrite [behaviour_with_drops5]
    rewrite [MLIR.run_seq_def]
    let st5 : State := (Γ st4 ⟦part5⟧)
    have h_st5 : st5 = (Γ st4 ⟦part5⟧) := rfl
    rewrite [←h_st5]
    rewrite [behaviour_with_drops6]
    rewrite [MLIR.run_seq_def]
    let st6 : State := (Γ st5 ⟦part6⟧)
    have h_st6 : st6 = (Γ st5 ⟦part6⟧) := rfl
    rewrite [←h_st6]
    rewrite [behaviour_with_drops7]
    rewrite [MLIR.run_seq_def]
    let st7 : State := (Γ st6 ⟦part7⟧)
    have h_st7 : st7 = (Γ st6 ⟦part7⟧) := rfl
    rewrite [←h_st7]
    rewrite [behaviour_with_drops8]
    rewrite [MLIR.run_seq_def]
    let st8 : State := (Γ st7 ⟦part8⟧)
    have h_st8 : st8 = (Γ st7 ⟦part8⟧) := rfl
    rewrite [←h_st8]
    rewrite [behaviour_with_drops9]
    rewrite [MLIR.run_seq_def]
    let st9 : State := (Γ st8 ⟦part9⟧)
    have h_st9 : st9 = (Γ st8 ⟦part9⟧) := rfl
    rewrite [←h_st9]
    rewrite [behaviour_with_drops10]
    rewrite [MLIR.run_seq_def]
    let st10 : State := (Γ st9 ⟦part10⟧)
    have h_st10 : st10 = (Γ st9 ⟦part10⟧) := rfl
    rewrite [←h_st10]
    rewrite [behaviour_with_drops11]
    rewrite [MLIR.run_seq_def]
    let st11 : State := (Γ st10 ⟦part11⟧)
    have h_st11 : st11 = (Γ st10 ⟦part11⟧) := rfl
    rewrite [←h_st11]
    rewrite [behaviour_with_drops12]
    rewrite [MLIR.run_seq_def]
    let st12 : State := (Γ st11 ⟦part12⟧)
    have h_st12 : st12 = (Γ st11 ⟦part12⟧) := rfl
    rewrite [←h_st12]
    rewrite [behaviour_with_drops13]
    rewrite [MLIR.run_seq_def]
    let st13 : State := (Γ st12 ⟦part13⟧)
    have h_st13 : st13 = (Γ st12 ⟦part13⟧) := rfl
    rewrite [←h_st13]
    rewrite [behaviour_with_drops14]
    rewrite [MLIR.run_seq_def]
    let st14 : State := (Γ st13 ⟦part14⟧)
    have h_st14 : st14 = (Γ st13 ⟦part14⟧) := rfl
    rewrite [←h_st14]
    rewrite [behaviour_with_drops15]
    rewrite [MLIR.run_seq_def]
    let st15 : State := (Γ st14 ⟦part15⟧)
    have h_st15 : st15 = (Γ st14 ⟦part15⟧) := rfl
    rewrite [←h_st15]
    rewrite [behaviour_with_drops16]
    rewrite [MLIR.run_seq_def]
    let st16 : State := (Γ st15 ⟦part16⟧)
    have h_st16 : st16 = (Γ st15 ⟦part16⟧) := rfl
    rewrite [←h_st16]
    rewrite [h_st16, ←MLIR.run_seq_def]
    rewrite [h_st15, ←MLIR.run_seq_def]
    rewrite [h_st14, ←MLIR.run_seq_def]
    rewrite [h_st13, ←MLIR.run_seq_def]
    rewrite [h_st12, ←MLIR.run_seq_def]
    rewrite [h_st11, ←MLIR.run_seq_def]
    rewrite [h_st10, ←MLIR.run_seq_def]
    rewrite [h_st9, ←MLIR.run_seq_def]
    rewrite [h_st8, ←MLIR.run_seq_def]
    rewrite [h_st7, ←MLIR.run_seq_def]
    rewrite [h_st6, ←MLIR.run_seq_def]
    rewrite [h_st5, ←MLIR.run_seq_def]
    rewrite [h_st4, ←MLIR.run_seq_def]
    rewrite [h_st3, ←MLIR.run_seq_def]
    rewrite [h_st2, ←MLIR.run_seq_def]
    rewrite [h_st1, ←MLIR.run_seq_def]
    rw [h_st0, ←MLIR.run_seq_def]
lemma getReturn_ignores_drops :
  getReturn (Γ st ⟦part0;part1;part2;part3;part4;part5;part6;part7;part8;part9;part10;part11;part12;part13;part14;part15;part16;dropfelt ⟨"%13"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩⟧) =
  getReturn (Γ st ⟦part0;part1;part2;part3;part4;part5;part6;part7;part8;part9;part10;part11;part12;part13;part14;part15;part16⟧) := by
    simp [getReturn, MLIR.run_seq_def, State.constraintsInVar, MLIR.run_dropfelt, State.dropFelts_buffers, State.dropFelts_props]

end Risc0.ComputeDecode.Constraints.Code