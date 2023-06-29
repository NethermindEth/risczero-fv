import Risc0.Basic

open Risc0

def ith_hot (n : ℕ) (i : ℕ) : BufferAtTime :=
  ((List.range n).map (Nat.cast ∘ Bool.toNat ∘ (Nat.beq i))).map some

def ith_hot_def {n : ℕ} {i : ℕ} : 
  ith_hot n i = ((List.range n).map (Nat.cast ∘ Bool.toNat ∘ (Nat.beq i))).map some := by rfl

def one_hot_spec (n : ℕ) (input : Felt) (output: BufferAtTime) : Prop := 
  ∃ (i : ℕ), i < n ∧ input = i ∧ output = ith_hot n i

def one_hot_direct_spec (n : ℕ) (input : Felt) (output: BufferAtTime) : Prop :=
  ∃ (i : ℕ), i < n ∧ input = i ∧ 
  output.get! i = (some 1) ∧ 
  output.length = n ∧ 
  ∀ j, j < n ∧ j ≠ i → output.get! j = (some 0) 

@[simp]
lemma ith_hot_len {n i : ℕ} :
  (ith_hot n i).length = n := by simp [ith_hot, List.length_map, List.length_map]

lemma ith_hot_get_succ₁ {n : ℕ} :
  ith_hot n.succ n = ith_hot n n ++ [some 1] := by
  rcases n with _ | n
  · simp [ith_hot]
  · generalize eq: ith_hot (Nat.succ n) (Nat.succ n) ++ [some 1] = rhs
    simp [ith_hot]
    rw [List.range_succ, List.map_append]
    simp
    simp [Bool.toNat]
    rw [←eq]
    simp [ith_hot]
    aesop

lemma ith_hot_get_succ₂ {n : ℕ} {i : ℕ} (h : i ≠ n) :
  ith_hot n.succ i = ith_hot n i ++ [some 0] := by
  simp [ith_hot]
  rcases n with _ | n
  · simp [ith_hot]
    cases i; try (trivial; simp [Nat.beq])
  · simp [List.range_succ, List.map_append, Bool.toNat]
    generalize eq: Nat.beq i n.succ = b
    rcases b
    simp [ite_true]
    have h_neq := Nat.eq_of_beq_eq_true eq
    tauto

@[simp]
lemma ith_hot_get_succ {n i : ℕ} :
  ith_hot n.succ i = ith_hot n i ++ [some (if i = n then 1 else 0)] := by
  by_cases eq: i = n
  · rw [eq, ith_hot_get_succ₁]
    simp
  · rw [ith_hot_get_succ₂ eq]
    aesop

lemma list_get! [Inhabited α] {n : ℕ} {l : List α} {j : ℕ} (h : j < n) : 
  n = l.length → List.get? l j = some (List.get! l j) := by
  revert j l n
  intros n
  apply (@Nat.strong_induction_on (λ n => ∀ l j, j < n → n = List.length l → List.get? l j = some (List.get! l j)) n)
  intros n ih l j hj_n hlen
  rcases l with _ | ⟨x, l⟩; try aesop 
  unfold List.get? List.get!
  rcases j with _ | j; try simp
  simp
  apply (ih n.pred); try aesop
  rw [Nat.lt_pred_iff]
  exact hj_n
  simp [hlen, List.length]

theorem get!_eq_get? [Inhabited α] {l : List α} {j : ℕ} (h : j < l.length) : 
  List.get? l j = some (List.get! l j) := by rw [list_get! h]; try rfl

@[simp]
lemma ith_hot_get {n : ℕ} {i j : ℕ} (h : j < n): 
   (ith_hot n i).get! j = some (if i = j then 1 else 0) := by
  apply List.get!_of_get?
  induction' n with n ih; try aesop
  rw [Nat.lt_succ_iff_lt_or_eq] at h
  rcases h with h | h
  · specialize (ih h)
    simp only [ith_hot_get_succ]
    rw [List.get?_append (by aesop), ih]
  · subst h
    simp [ith_hot_get_succ]
    rw [List.get?_append_right (by aesop)]
    simp

lemma one_hot_direct_spec_of_one_hot_spec {n : ℕ} {input : Felt} {output: BufferAtTime} :
  one_hot_spec n input output ↔ one_hot_direct_spec n input output := by
  unfold one_hot_direct_spec one_hot_spec
  apply Iff.intro
  · rintro ⟨i, h₁, h₂, h₃⟩ 
    exists i
    subst h₃
    aesop
  · rintro ⟨i, h₁, h₂, h₃, h₄, h₅⟩
    exists i
    aesop
    apply @List.ext _ output (ith_hot _ i)
    intros j
    by_cases j_le : j < output.length
    · rw [get!_eq_get? j_le, 
        get!_eq_get? (by simp; exact j_le),
        ith_hot_get (by aesop)]
      aesop
    · have h_lhs : List.get? output j = none := by aesop
      have h_rhs : List.get? (ith_hot output.length i) j = none := by aesop
      rw [h_lhs, h_rhs]

