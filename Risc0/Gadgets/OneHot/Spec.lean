import Risc0.Cirgen

open Risc0

def ith_hot (n : ℕ) (i : ℕ) : BufferAtTime :=
  ((List.range n).map (Nat.cast ∘ Bool.toNat ∘ (Nat.beq i))).map some

def ith_hot_simple (n i : ℕ) : BufferAtTime := (List.replicate n (some 0)).set i (some 1)

def ith_hot_def {n : ℕ} {i : ℕ} : 
  ith_hot n i = ((List.range n).map (Nat.cast ∘ Bool.toNat ∘ (Nat.beq i))).map some := rfl

def one_hot_spec (n : ℕ) (input : Felt) (output: BufferAtTime) : Prop := 
  ∃ (i : ℕ), i < n ∧ input = i ∧ output = ith_hot n i

def one_hot_direct_spec (n : ℕ) (input : Felt) (output: BufferAtTime) : Prop :=
  ∃ (i : ℕ), i < n ∧ input = i ∧ 
  output.get! i = some 1 ∧ 
  output.length = n ∧ 
  ∀ j, j < n ∧ j ≠ i → output.get! j = some 0

lemma List.replicate_n_same_comm :
  a :: List.replicate n a = List.replicate n a ++ [a] := by
  induction n with
    | zero => simp
    | succ n ih => simp; exact ih

@[simp]
lemma ith_hot_simple_get_succ {n i : ℕ} :
  ith_hot_simple n.succ i = ith_hot_simple n i ++ [some (if i = n then 1 else 0)] := by
  unfold ith_hot_simple
  by_cases eq : i = n
  · subst eq
    simp
    induction i with
      | zero => simp
      | succ i ih => simp [ih]
  · simp
    induction i generalizing n with
      | zero => simp [eq]
                cases n <;> aesop
                simp [List.set]
                exact List.replicate_n_same_comm
      | succ i ih => cases n <;> aesop

@[simp]
lemma ith_hot_len {n i : ℕ} :
  (ith_hot n i).length = n := by simp [ith_hot, List.length_map, List.length_map]

lemma ith_hot_get_succ₁ {n : ℕ} :
  ith_hot n.succ n = ith_hot n n ++ [some 1] := by
  rcases n with _ | n <;> simp [ith_hot]
  · simp [ith_hot]; rw [List.range_succ, List.map_append]
    aesop

lemma ith_hot_get_succ₂ {n : ℕ} {i : ℕ} (h : i ≠ n) :
  ith_hot n.succ i = ith_hot n i ++ [some 0] := by
  simp [ith_hot]
  rcases n with _ | n
  · simp [ith_hot]; cases i <;> aesop
  · simp [List.range_succ, List.map_append, Bool.toNat]
    by_cases eq : Nat.beq i n.succ <;> simp [eq]; aesop

@[simp]
lemma ith_hot_get_succ {n i : ℕ} :
  ith_hot n.succ i = ith_hot n i ++ [some (if i = n then 1 else 0)] := by
  by_cases eq: i = n
  · rw [eq, ith_hot_get_succ₁]
    simp
  · rw [ith_hot_get_succ₂ eq]
    aesop

theorem ith_hot_eq_ith_hot_simple : ith_hot n i = ith_hot_simple n i := by
  induction n with
    | zero => simp [ith_hot, ith_hot_simple]
    | succ n ih => rw [ith_hot_simple_get_succ, ith_hot_get_succ, ih]

lemma List.list_get! [Inhabited α] {n : ℕ} {l : List α} {j : ℕ} (h : j < n) : 
  n = l.length → List.get? l j = some (List.get! l j) := by
  induction n generalizing j l with
    | zero => aesop
    | succ k ih => intros h₁
                   rcases l <;> rcases j <;> try aesop
                   rw [ih (Nat.lt_of_succ_lt_succ h) rfl]

theorem List.get!_eq_get? [Inhabited α] {l : List α} {j : ℕ} (h : j < l.length) : 
  List.get? l j = some (List.get! l j) := by rw [list_get! h]; try rfl

@[simp]
lemma ith_hot_get {n : ℕ} {i j : ℕ} (h : j < n): 
   (ith_hot n i).get! j = some (if i = j then 1 else 0) := by
  rw [ith_hot_eq_ith_hot_simple]
  simp [ith_hot_simple]
  apply List.get!_of_get?
  rw [List.get?_eq_get (by aesop),
      List.get_set,
      List.get_replicate,
      ←apply_ite]

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
    · rw [List.get!_eq_get? j_le, 
        List.get!_eq_get? (by simp; exact j_le),
        ith_hot_get (by aesop)]
      aesop
    · have h_lhs : List.get? output j = none := by aesop
      have h_rhs : List.get? (ith_hot output.length i) j = none := by aesop
      rw [h_lhs, h_rhs]

