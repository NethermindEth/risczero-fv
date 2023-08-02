import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas
import Mathlib.Data.Vector.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.Nat.ModEq
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Data.Vector.Basic
import Risc0.Wheels

instance {n} : HShiftRight (Bitvec n) ℕ (Bitvec n) := ⟨Bitvec.ushr⟩
instance {n} : HShiftRight (Vector Bool n) ℕ (Bitvec n) := ⟨Bitvec.ushr⟩
instance {n} : HAnd (Bitvec n) (Bitvec n) (Bitvec n) := ⟨Bitvec.and⟩

prefix:max "←ℕ" => Bitvec.ofNat 32
prefix:max "→ℕ" => Bitvec.toNat

instance {n} : HAnd (Bitvec n) (Bitvec n) (Bitvec n) := ⟨Bitvec.and⟩

@[simp]
theorem Vector.map₂_cons (hd₁ : α) (tl₁ : Vector α n) (hd₂ : β) (tl₂ : Vector β n) (f : α → β → γ) :
    Vector.map₂ f (hd₁ ::ᵥ tl₁) (hd₂ ::ᵥ tl₂) = f hd₁ hd₂ ::ᵥ (Vector.map₂ f tl₁ tl₂) :=
  rfl

@[simp]
theorem Vector.get_map₂ (v₁ : Vector α n) (v₂ : Vector β n) (f : α → β → γ) (i : Fin n) :
    get (map₂ f v₁ v₂) i = f (get v₁ i) (get v₂ i) := by
  clear * - v₁ v₂
  induction v₁, v₂ using inductionOn₂
  case nil =>
    exact Fin.elim0 i
  case cons x xs y ys ih =>
    rw [map₂_cons]
    cases i using Fin.cases
    . simp only [get_zero, head_cons]
    . simp only [get_cons_succ, ih]

def allOnes (n : ℕ) : ℕ := 2 ^ n - 1

@[simp] lemma all_ones_div_two {n : ℕ} : allOnes n.succ / 2 = allOnes n :=
  by simp [allOnes, pow_succ, Nat.mul_sub_div]

@[simp] lemma all_ones_succ {n : ℕ} : allOnes n.succ = 2 * (allOnes n) + 1 := by
  unfold allOnes
  have eq₁ : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have eq₂ : 1 ≤ 2 ^ n.succ := Nat.one_le_pow _ _ (by linarith)
  zify [eq₁, eq₂]
  simp [pow_succ]
  ring_nf
  trivial

@[simp] lemma all_ones_succ_mod_2 {n : ℕ} :
  allOnes n.succ % 2 = 1 := by simp [Nat.add_mod]

lemma all_ones_contains_only_ones {n i : ℕ} (h : i < n) :
  (Bitvec.ofNat n (allOnes n)).toList.get? i = some true := by
  induction' n with n ih; try trivial
  unfold Bitvec.ofNat
  simp
  by_cases eq : i = n
  · subst eq
    rw [List.get?_append_right (by simp)]
    simp
    simp [Nat.add_mod, Nat.mul_mod]
  · have h : i < n := by 
      cases (Nat.lt_or_eq_of_le (Nat.lt_succ.mp h)); try trivial; try aesop
    rw [List.get?_append (by simp [h]),
      ←all_ones_succ, 
      all_ones_div_two, ih h] 

@[simp]
lemma Bitvec.ofNat_zero_get_eq_zero {n i : ℕ} (h : i < n) : 
  (Bitvec.ofNat n 0).toList.get? i = some false := by
  induction' n with n ih; try trivial
  unfold Bitvec.ofNat
  simp
  by_cases eq : i = n; try 
  · subst eq
    rw [List.get?_append_right (by simp)]
    simp
  · have h : i < n := by 
      cases (Nat.lt_or_eq_of_le (Nat.lt_succ.mp h)); try trivial; try aesop
    rw [List.get?_append (by simp [h]), ih h]

lemma allOnes_toList_get?_higher_eq_zero {n m i : ℕ} (h : n ≤ m) (h' : i < m - n) :
  (Bitvec.ofNat m (allOnes n)).toList.get? i = some false := by
  induction' n with n ih generalizing m i
  · simp [allOnes]
    rw [Bitvec.ofNat_zero_get_eq_zero (by {
      simp at h'
      exact h'
    })]
  · rcases m with _ | m; try trivial
    simp at h'
    unfold Bitvec.ofNat
    rw [Vector.toList_append, 
        List.get?_append (Nat.lt_of_lt_of_le h' (by aesop)),
        all_ones_div_two,
        ih (Nat.le_of_succ_le_succ h) h']



theorem allOnes_get_higher_eq_zero {n m i : ℕ} (h : n ≤ m) (h' : i < m - n) :
  (Bitvec.ofNat m (allOnes n)).get ⟨i, by {
    exact Nat.lt_of_lt_of_le h' (by aesop)
  }⟩ = false := by
  rw [Vector.get_eq_get,
      ←Option.some_inj,
      ←List.get?_eq_get]
  simp [allOnes_toList_get?_higher_eq_zero h h']


lemma Bitvec.ofNat_toList_reverse_n_get_eq_ofNat_m_get {x n m i : ℕ} (h : i < n) (h' : n ≤ m) :
  (Bitvec.ofNat n x).toList.reverse.get? i  = (Bitvec.ofNat m x).toList.reverse.get? i := by
  revert n m i
  induction x using Nat.case_strong_induction_on with
  | hz => 
      intros n m i h h'
      rw [List.get?_reverse _ (by simp [h]), List.get?_reverse _ (by simp; exact Nat.lt_of_lt_of_le h h')]
      rcases n with _ | n; try trivial
      simp
      rw [Bitvec.ofNat_zero_get_eq_zero (by {
        apply Nat.lt_of_le_of_lt
        apply Nat.sub_le
        aesop
      })]
      rw [Bitvec.ofNat_zero_get_eq_zero (by {
        apply Nat.lt_of_le_of_lt
        apply Nat.sub_le
        apply Nat.sub_lt
        have h'' := Nat.lt_of_lt_of_le h h'
        apply Nat.lt_of_le_of_lt (Nat.zero_le i) h''
        aesop
      })]
  | hi x ih => 
    intros n m i h h'
    unfold Bitvec.ofNat
    rcases n with _ | n; try aesop
    rcases m with _ | m; try aesop
    simp
    rcases i with _ | i; try aesop
    simp
    rw [ih _ (Nat.le_of_lt_succ 
      (Nat.div_lt_self (by linarith) (by simp))) 
      (Nat.lt_of_succ_lt_succ h)
      (Nat.le_of_succ_le_succ h')]
    
theorem Bitvec.ofNat_reverse_n_get_eq_ofNat_m_get {x n m i : ℕ} (h : i < n) (h' : n ≤ m) :
  (Bitvec.ofNat n x).reverse.get ⟨i, h⟩  = (Bitvec.ofNat m x).reverse.get ⟨i, Nat.lt_of_lt_of_le h h'⟩ := by
  rw [Vector.get_eq_get]
  simp [List.get_eq_iff,
      Vector.toList_reverse,
      Bitvec.ofNat_toList_reverse_n_get_eq_ofNat_m_get h h']
  rw [←Vector.toList_reverse]
  have hᵢ: i = ↑(⟨i, by exact (Nat.lt_of_lt_of_le h (by simp [h']))⟩ : Fin (List.length (Vector.toList (Vector.reverse (Bitvec.ofNat m x))))) := rfl
  generalize eq : some (Vector.get (Vector.reverse (Bitvec.ofNat m x)) { val := i, isLt := (_ : i < m) }) = t
  rw [hᵢ]
  subst eq
  rw [←List.get_eq_iff,
      Vector.get_eq_get]
  simp

theorem Bitvec.ofNat_n_toList_get_eq_ofNat_m_get {x n m i : ℕ} (h : i < n) (h' : n ≤ m) :
  (Bitvec.ofNat n x).toList.get? i  = (Bitvec.ofNat m x).toList.get? ((m - n) + i) := by
  rcases n with n | n; try trivial
  have h'' := @Bitvec.ofNat_toList_reverse_n_get_eq_ofNat_m_get x n.succ m (n - i) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by aesop)) h'
  have h_i : (n - (n - i)) = i := by
    rw [Nat.sub_sub_self (by simp; linarith)]
  rw [List.get?_reverse _ (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self n)) (by simp[h']))] at h''
  simp at h''
  rw [h_i] at h''
  rw [h'',
      List.get?_reverse _ (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by simp [Nat.lt_of_succ_le h']))]
  simp
  have h_m_i : m - 1 - (n - i) = m - n.succ + i := by
    rcases m with m | m; try trivial
    simp
    apply Nat.sub_eq_of_eq_add
    rw [←Nat.add_sub_assoc (Nat.le_of_lt_succ h),
        Nat.add_assoc (m - n),
        Nat.add_comm i n,
        ←Nat.add_assoc (m - n),
        Nat.sub_add_cancel (Nat.le_of_succ_le_succ h'),
        Nat.add_sub_cancel]
  rw [h_m_i]

theorem Bitvec.ofNat_n_get_eq_ofNat_m_get {x n m i : ℕ} (h : i < n) (h' : n ≤ m) :
  (Bitvec.ofNat n x).get ⟨i, h⟩  = (Bitvec.ofNat m x).get ⟨(m - n) + i, by {
    rcases n with _ | n; try trivial
    rcases m with _ | m; try trivial
    simp at *
    rw [←Nat.sub_add_comm (by exact Nat.le_of_succ_le_succ h')]
    apply Nat.lt_of_le_of_lt
    apply Nat.sub_le_sub_left _ (Nat.le_of_lt_succ h)
    simp   
  }⟩ := by
  rw [Vector.get_eq_get,
      Vector.get_eq_get,
      ←List.get_reverse _ _ 
      (by rcases n with _ | n; try trivial; simp [Nat.lt_of_le_of_lt (Nat.sub_le n i)]),
      ←List.get_reverse (Vector.toList (Bitvec.ofNat m x)) _
      (by {
        rcases n with _ | n; try trivial
        rcases m with _ | m; try trivial
        simp
        exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by simp)
      })]
  simp
  have h_rev := @Bitvec.ofNat_toList_reverse_n_get_eq_ofNat_m_get x n m 
    (n - 1 - i) (by {
      rcases n with _ | n; try trivial
      simp
      exact Nat.lt_of_le_of_lt (Nat.sub_le n i) (by simp)
    }) h'
  simp
  rw [List.get_eq_iff]
  simp
  rw [h_rev]
  have h_n_m : (n - 1 - i) = m - 1 - (m - n + i) := by rw [←Nat.sub_sub,
        Nat.sub_sub m 1,
        Nat.add_comm,
        ←Nat.sub_sub m,
        Nat.sub_sub_self h']
  rw [h_n_m, List.get?_eq_get]

-- theorem Bitvec.ofNat_n_get_eq_ofNat_m_get {x n m i : ℕ} (h : i < n) (h' : n ≤ m) :
--   (Bitvec.ofNat n x).get ⟨i, h⟩  = (Bitvec.ofNat m x).get ⟨(m - n) + i, by {
--     rcases n with _ | n; try trivial
--     rcases m with _ | m; try trivial
--     simp at *
--     rw [←Nat.sub_add_comm (by exact Nat.le_of_succ_le_succ h')]
--     apply Nat.lt_of_le_of_lt
--     apply Nat.sub_le_sub_left _ (Nat.le_of_lt_succ h)
--     simp   
--   }⟩ := by


theorem Bitvec.ofNat_n_get_eq_ofNat_m_get' {x n m : ℕ} {i : Fin n} (h' : n ≤ m) :
  (Bitvec.ofNat n x).get i  = (Bitvec.ofNat m x).get ⟨(m - n) + i, by {
    rcases i with ⟨i, h⟩ 
    rcases n with _ | n; try trivial
    rcases m with _ | m; try trivial
    simp
    simp at *
    rw [←Nat.sub_add_comm (by exact Nat.le_of_succ_le_succ h')]
    apply Nat.lt_of_le_of_lt
    apply Nat.sub_le_sub_left _ (Nat.le_of_lt_succ h)
    simp   
  }⟩ := by
    rcases i with ⟨i, h⟩
    rw [Bitvec.ofNat_n_get_eq_ofNat_m_get _ h']

lemma Bitvec.allOnes_get' {m n : ℕ} {i : Fin m} (h' : n ≤ m) : Vector.get (Bitvec.ofNat m (allOnes n)) i = Nat.ble (m - n) i.val := by 
  rcases i with ⟨i, h⟩
  simp
  by_cases h_lt : i < m - n
  · rw [allOnes_get_higher_eq_zero h' h_lt]
    generalize eq: Nat.ble (m - n) i = s
    cases s; try aesop
    rw [Nat.ble_eq] at eq
    have h'' := Nat.lt_of_le_of_lt eq h_lt
    aesop
  · rw [Nat.not_lt] at h_lt
    rw [Vector.get_eq_get]
    rw [←Option.some_inj]
    rw [←List.get?_eq_get]
    simp
    have h_i : i = (m - n) + (i - (m - n)) := by aesop
    generalize eq_lhs : some (Nat.blt (m - n) i) = lhs
    rw [h_i]
    subst eq_lhs
    have h_i_lt_n : i - (m - n) < n := Nat.sub_lt_left_of_lt_add (by linarith) (by {
        rw [←Nat.sub_add_comm h',
            Nat.add_sub_cancel]
        exact h
      })
    rw [←Bitvec.ofNat_n_toList_get_eq_ofNat_m_get h_i_lt_n h',
        all_ones_contains_only_ones h_i_lt_n]
    simp
    symm
    rw [Nat.ble_eq, ←h_i]
    exact h_lt

lemma Bitvec.allOnes_get {m n : ℕ} {i : Fin m} : Vector.get (Bitvec.ofNat m (allOnes n)) i = Nat.ble (m - n) i.val := by   
  by_cases h' : n ≤ m
  · rw [Bitvec.allOnes_get' h']
  · simp at h' 
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt h')]
    have h : 0 ≤ (↑i : ℕ) := by simp
    rw [←Nat.ble_eq] at h
    rw [h]
    rcases i with ⟨i, hi⟩
    rw [Bitvec.ofNat_n_get_eq_ofNat_m_get hi (Nat.le_of_lt h')]
    rw [Bitvec.allOnes_get' (by simp)]
    simp

theorem Bitvec.and_allOnes_eq_get' {n m : ℕ} {x : Bitvec m} {i : Fin m} (h : n ≤ m): 
  (x &&& (Bitvec.ofNat m (allOnes n))).get i = if i < m - n then false else x.get i := by
  rcases i with ⟨i, h'⟩ 
  dsimp [(· &&& ·)]
  unfold Bitvec.and
  simp
  rw [Bitvec.allOnes_get' h]
  simp
  by_cases h'' : i < m - n
  · aesop'
    generalize eq : Nat.ble (m - n) i = ble
    rcases ble; try tauto
    rw [Nat.ble_eq] at eq
    have h''' := Nat.lt_of_le_of_lt eq h''
    linarith
  · have h''' := Nat.le_of_not_lt h''
    rw [←Nat.ble_eq] at h'''
    simp [h''']
    symm
    rw [ite_eq_iff]
    right
    exact ⟨h'', rfl⟩

theorem Bitvec.and_allOnes_eq_get {n m : ℕ} {x : Bitvec m} {i : Fin m}: 
  (x &&& (Bitvec.ofNat m (allOnes n))).get i = if i < m - n then false else x.get i := by
  by_cases h : n ≤ m
  · rw [Bitvec.and_allOnes_eq_get' h]
  · dsimp [(· &&& ·)]; unfold Bitvec.and
    simp
    rw [Bitvec.allOnes_get]
    simp at h
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt h)]
    simp
    have h : 0 ≤ (↑i : ℕ) := by simp
    rw [←Nat.ble_eq] at h
    rw [h]
    simp


theorem List.get?_eq_of_eq_vals {l : List α} {i j : Fin (l.length)} :  
  i.val = j.val → l.get i = l.get j := by
  intros eq
  rcases i with ⟨i, h⟩
  rcases j with ⟨j, h'⟩
  simp at eq
  induction' l with x l ih generalizing i j; try trivial
  simp
  rcases i with _ | i; try aesop
  rcases j with _ | j; try aesop
  simp
  rw [ih i (Nat.lt_of_succ_lt_succ h) j (Nat.lt_of_succ_lt_succ h')]
  aesop

theorem Vector.get_eq_of_eq_vals {n : ℕ} {v : Vector α n} {i j : Fin n} :  
  i.val = j.val → v.get i = v.get j := by
  intros eq
  rw [Vector.get_eq_get,
      Vector.get_eq_get,
      List.get?_eq_of_eq_vals]
  simp [eq]

theorem Bitvec.get_cong {n m : ℕ} {x : Bitvec n} {i : Fin n} {j : Fin m} (h : n = m) (h' : i.val = j.val) :
  (x.cong h).get j = x.get i := by 
  unfold Bitvec.cong
  rw [Vector.get_eq_get]
  rw [Vector.get_eq_get]
  rcases x with ⟨x, h⟩
  simp
  apply List.get?_eq_of_eq_vals
  simp [h']

lemma Option.map₂_map {f : α → β → γ} {x : Option α} {y : Option β}: 
  Option.map₂ f x y =
    Option.bind (Option.map f x) fun g => Option.map g y := by 
  unfold map₂ Option.bind
  aesop


theorem List.get?_replicate {α : Type u_1} {a : α} {n : Nat} {m : ℕ} (h : m < n) :
  List.get? (List.replicate n a) m = some a := by
  rw [List.get?_eq_get (by simp [h])]
  simp

theorem Bitvec.ushr_full_length {n m : ℕ} {x : Bitvec n} (h : n ≤ m) :
  x >>> m = Vector.replicate n false := by
  dsimp [(·>>>·), ushr, fillShr]
  apply Vector.ext
  intro i
  rw [@Bitvec.get_cong _ _ _ ⟨i, by {
    simp
    rw [Nat.add_comm, Nat.sub_add_min_cancel]
    exact i.isLt
  }⟩ _ (by {
    simp
    rw [Nat.add_comm, Nat.sub_add_min_cancel]
  }) (by simp)]
  rw [Vector.get_eq_get,
      Vector.get_eq_get,
      ←Option.some_inj,
      ←List.get?_eq_get,
      ←List.get?_eq_get]
  unfold Vector.replicate
  simp
  rw [List.get?_append (by {
    simp
    exact (Nat.lt_of_lt_of_le i.isLt h)
  })]
  rw [Nat.min_eq_left h]
  

theorem Bitvec.ushr_alternative₁ {n m : ℕ} {x : Bitvec n} {i : Fin n} (h : i < m) :
  (x >>> m).get i = false := by
  by_cases le : n ≤ m
  · rw [Bitvec.ushr_full_length le]
    rw [Vector.get_eq_get, ←Option.some_inj]
    unfold Vector.replicate
    simp
  · have h_lt := Nat.lt_of_not_le le
    dsimp [(·>>>·), ushr, fillShr]
    rw [@Bitvec.get_cong _ _ _ ⟨i, by {
      simp
      rw [Nat.add_comm, Nat.sub_add_min_cancel]
      exact Nat.lt_trans h h_lt
    }⟩ _ (by {
      simp
      rw [Nat.add_comm, Nat.sub_add_min_cancel]
    }) (by simp)]
    rw [Vector.get_eq_get, ←Option.some_inj]
    rw [←List.get?_eq_get]
    unfold Vector.replicate
    simp
    rw [List.get?_append (by simp [h]),
        List.get?_replicate]
    simp [h]

theorem Bitvec.ushr_alternative₂ {n m : ℕ} {x : Bitvec n} {i : Fin n} (h : m ≤ i) :
  (x >>> m).get i = x.get ⟨i - m, Nat.lt_of_le_of_lt (Nat.sub_le _ _) (i.isLt)⟩ := by
  by_cases le : n ≤ m
  · rcases i with ⟨i, h_i⟩
    simp at *
    linarith
  · have h_lt := Nat.lt_of_not_le le
    dsimp [(·>>>·), ushr, fillShr]
    rw [@Bitvec.get_cong _ _ _ ⟨i, by {
      simp
      rw [Nat.add_comm, Nat.sub_add_min_cancel]
      exact i.isLt
    }⟩ _ (by {
      simp
      rw [Nat.add_comm, Nat.sub_add_min_cancel]
    }) (by simp)]
    rw [Vector.get_eq_get, ←Option.some_inj]
    rw [←List.get?_eq_get]
    unfold Vector.replicate
    simp
    rw [List.get?_append_right (by {
      simp
      right
      exact h
    })]
    rw [List.get?_take (by {
      simp
      rw [Nat.min_eq_right (Nat.le_of_lt h_lt)]
      apply Nat.lt_sub_of_add_lt
      rw [Nat.sub_add_cancel h]
      exact i.isLt
    })]
    simp
    rw [Nat.min_eq_right (Nat.le_of_lt h_lt)]
    rw [Vector.get_eq_get]
    rw [List.get?_eq_get (by {
      simp
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt
    })]
    simp

-- Boy are dependent types fun or what? (Shoudl be simp but breaks proofs.)
lemma Vector.nil_append {vec₁ : Vector α 0} {vec₂ : Vector α n} :
  Vector.append vec₁ vec₂ =
    ⟨vec₂.toList,
      of_eq_true ((congr (congrArg Eq (toList_length vec₂)) (zero_add n)).trans (eq_self n))
    ⟩ := by
  cases vec₂; rcases vec₁ with ⟨_ | ⟨_, _⟩, contra⟩
  · simp [append]
  · congr; simp at contra

@[simp]
theorem Bitvec.ushr_zero {n : ℕ} {x : Bitvec n} : 
  x >>> 0 = x := by
  dsimp [(·>>>·), ushr, fillShr]; congr <;> simp
  rcases x with ⟨x, h⟩; rw [min_zero]; simp [Vector.nil_append]
  congr <;> simp [h]; aesop

theorem Bitvec.ushr_and_commute {n m : ℕ} {x y : Bitvec n} : 
  (x &&& y) >>> m = (x >>> m) &&& (y >>> m) := by
  apply Vector.ext
  rintro ⟨i, h⟩ 
  by_cases lt : i < m
  · dsimp [(· &&& ·), Bitvec.and]
    rw [Bitvec.ushr_alternative₁ (by simp[lt]),
        Vector.get_map₂,
        Bitvec.ushr_alternative₁ (by simp[lt])]
    simp
  · have lt := Nat.le_of_not_lt lt
    rw [Bitvec.ushr_alternative₂ (by simp[lt])]
    dsimp [(· &&& ·), Bitvec.and]
    rw [Vector.get_map₂,
        Vector.get_map₂,
        Bitvec.ushr_alternative₂ (by simp[lt]),
        Bitvec.ushr_alternative₂ (by simp[lt])]
  --     · 

lemma List.list_get! [Inhabited α] {n : ℕ} {l : List α} {j : ℕ} (h : j < n) : 
  n = l.length → List.get? l j = some (List.get! l j) := by
  induction n generalizing j l with
    | zero => aesop
    | succ k ih => intros h₁
                   rcases l <;> rcases j <;> try aesop'
                   rw [ih (Nat.lt_of_succ_lt_succ h) rfl]

theorem List.get!_eq_get? [Inhabited α] {l : List α} {j : ℕ} (h : j < l.length) : 
  List.get? l j = some (List.get! l j) := by rw [list_get! h]; try rfl

theorem Bitvec.allOnes_eq_cons {n m : ℕ} (h : n ≤ m):
  Bitvec.ofNat m.succ (allOnes n) = false ::ᵥ Bitvec.ofNat m (allOnes n) := by
  apply Vector.ext
  rintro ⟨i, h'⟩
  rw [Bitvec.allOnes_get]
  rcases i with _ | i
  · simp
    generalize eq : Nat.ble (Nat.succ m - n) 0 = s
    cases s; try trivial
    rw [Nat.ble_eq, Nat.le_zero_eq] at eq
    have eq := Nat.le_of_sub_eq_zero eq
    linarith
  · simp
    rw [@Vector.get_eq_of_eq_vals _ _ _ _ (Fin.succ ⟨i, Nat.lt_of_succ_lt_succ h'⟩) (by rfl)]
    rw [Vector.get_cons_succ]
    rw [Bitvec.allOnes_get]
    simp
    generalize eq : Nat.ble (Nat.succ m - n) (Nat.succ i) = s
    generalize eq' : Nat.ble (m - n) i = s'
    cases s; cases s'; try trivial
    · rw [Nat.ble_eq] at eq'
      have eq' := Nat.succ_le_succ eq'
      rw [←Nat.succ_sub h] at eq'
      rw [←Nat.ble_eq] at eq'
      rw [eq] at eq'
      cases eq'
    · rw [Nat.ble_eq] at eq
      rw [Nat.succ_sub h] at eq
      have eq := Nat.le_of_succ_le_succ eq
      rw [←Nat.ble_eq] at eq
      rw [eq'] at eq
      rw [eq]

theorem Bitvec.and_comm {n : ℕ} {x y : Bitvec n} :
  x &&& y = y &&& x := by
  dsimp [(· &&& ·), Bitvec.and]
  apply Vector.ext
  rintro ⟨m, h⟩
  rw [Vector.get_map₂, Vector.get_map₂, Bool.and_comm]

theorem Bitvec.and_assoc {n : ℕ} {x y z : Bitvec n} : 
  (x &&& y) &&& z = x &&& (y &&& z) := by
  dsimp [(· &&& ·), Bitvec.and]
  apply Vector.ext
  rintro ⟨m, h⟩
  rw [Vector.get_map₂, Vector.get_map₂, Vector.get_map₂, Vector.get_map₂, Bool.and_assoc]

@[simp]
theorem Vector.replicate_succ (val : α) :
    replicate (n+1) val = val ::ᵥ (replicate n val) :=
  rfl

@[simp]
theorem Vector.toList_replicate (val : α) :
  (replicate n val).toList = List.replicate n val := by rfl

theorem Bitvec.ofNat_zero_eq_replicate {n : ℕ} :
  Bitvec.ofNat n 0 = Vector.replicate n false := by
  induction n using Nat.case_strong_induction_on with
  | hz => aesop
  | hi x ih => 
    rw [Bitvec.ofNat_succ]
    simp
    rw [ih x (Nat.le_refl x)]
    apply Vector.ext
    rintro ⟨m, h⟩
    rw [Vector.get_eq_get, Vector.get_eq_get]
    rw [←Option.some_inj]
    rw [←List.get?_eq_get, ←List.get?_eq_get]
    simp
    by_cases eq : m = x
    · subst eq
      rw [List.get?_append_right (by simp)]
      simp
      have h_aux : (false :: List.replicate m false) = List.replicate m.succ false := by rfl
      rw [h_aux]
      rw [List.get?_replicate (by aesop)]
    · have h := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) eq
      rw [List.get?_append (by simp[h])]
      rw [List.get?_replicate (by aesop)]
      have h_aux : (false :: List.replicate x false) = List.replicate x.succ false := by rfl
      rw [h_aux]
      rw [List.get?_replicate (by aesop)]

@[simp]
theorem Bitvec.toNat_replicate_false_eq_zero {n : ℕ}  :
  Bitvec.toNat (Vector.replicate n false) = 0 := by
  rw [←Bitvec.ofNat_zero_eq_replicate,
      Bitvec.toNat_ofNat]
  simp

@[simp]
theorem Bitvec.replicate_zero_and_x_eq_replicate_zero {n : ℕ} {x : Bitvec n} :
  (Vector.replicate n false) &&& x = Vector.replicate n false := by
  dsimp [(· &&& ·), Bitvec.and]
  apply Vector.ext
  intros m
  simp [Vector.get_map₂, Vector.get_replicate]

theorem Bitvec.eq_zero_of_toNat_eq_zero {n : ℕ} {x : Bitvec n} (h: x.toNat = 0):
  x = Vector.replicate n false := by 
  rw [←Bitvec.ofNat_toNat x,
      h,
      Bitvec.ofNat_zero_eq_replicate]

def oneBitSet (n : ℕ) := 2 ^ n

lemma oneBitSet_mod_2 {n : ℕ} (h : 0 < n):
  oneBitSet n % 2 = 0 := by
  cases n; try aesop
  simp [oneBitSet, Nat.pow_succ, Nat.mul_mod]

lemma oneBitSet_div_2 {n : ℕ}:
  oneBitSet n.succ / 2 = oneBitSet n := by simp [oneBitSet, Nat.pow_succ]

def oneBitSetVec (n : ℕ) (m : Fin n) : Bitvec n := Vector.set (Vector.replicate n false) m true

theorem Bitvec.ofNat_oneBitSet_eq_oneBitSetVec {n : ℕ} {m : Fin n} :
  Bitvec.ofNat n (oneBitSet m.val) = oneBitSetVec n ⟨n - m.val - 1, by {
    simp
    apply Nat.lt_of_lt_of_le
    apply Nat.sub_lt
    apply Nat.lt_sub_of_add_lt
    simp
    linarith
    apply Nat.sub_le
  }⟩ := by
  induction' n with n ih; try simp
  rw [Bitvec.ofNat_succ]
  apply Vector.ext
  rintro ⟨i, h'⟩  
  unfold oneBitSetVec
  rw [Vector.get_set_eq_if]
  rcases m with ⟨m, h⟩
  simp
  rcases m with _ | m
  · simp [oneBitSet]
    have h_eq : (1 : ℕ) / (2 : ℕ) = 0 := by simp
    rw [h_eq]
    rw [Bitvec.ofNat_zero_eq_replicate]
    rw [Vector.get_eq_get]
    rw [←Option.some_inj]
    rw [←List.get?_eq_get]
    simp
    by_cases eq: n = i
    · subst eq
      simp
      rw [List.get?_append_right (by simp)]
      simp
    · rw [List.get?_append (by {
        simp
        exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h') (by aesop)
      })]
      rw [List.get?_replicate (by {
        simp
        exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h') (by aesop)
      })]
      simp
      symm 
      rw [ite_eq_iff]
      right
      simp [eq]
      rw [Vector.get_eq_get]
      rw [←Option.some_inj]
      rw [←List.get?_eq_get]
      simp
      have h_aux : (false :: List.replicate n false) = List.replicate n.succ false := by rfl
      rw [h_aux]
      rw [List.get?_replicate h']
  · rw [oneBitSet_div_2,
        oneBitSet_mod_2 (by linarith)]
    simp
    rw [Vector.get_eq_get]
    rw [←Option.some_inj]
    rw [←List.get?_eq_get]
    simp
    rw [@ih ⟨m, by linarith⟩]
    simp
    unfold oneBitSetVec
    simp
    by_cases eq: i = n - m - 1
    · subst eq
      simp
      rw [List.get?_append (by {
        simp
        apply Nat.lt_of_lt_of_le
        apply Nat.sub_lt
        apply Nat.lt_sub_of_add_lt
        simp
        linarith
        linarith
        apply Nat.sub_le
      })]
      rw [List.get?_set]
      simp
      left
      rw [List.get?_replicate (by {
        simp
        apply Nat.lt_of_lt_of_le
        apply Nat.sub_lt
        apply Nat.lt_sub_of_add_lt
        simp
        linarith
        linarith
        apply Nat.sub_le
      })]
    · by_cases eq' : i = n
      · subst eq'
        simp
        rw [List.get?_append_right (by simp)]
        simp
        symm
        rw [ite_eq_iff]
        right
        aesop'
        rw [Vector.get_eq_get]
        rw [←Option.some_inj]
        rw [←List.get?_eq_get]
        simp
        have h_aux : (false :: List.replicate i false) = List.replicate i.succ false := by rfl
        rw [h_aux]
        rw [List.get?_replicate (by simp)]
      · rw [List.get?_append (by {
          simp
          simp
          exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h') (by aesop)
        })]
        rw [List.get?_set_ne _ _ (by aesop)]
        rw [List.get?_replicate (by {
          simp
          exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h') (by aesop)
        })]
        simp
        symm
        rw [ite_eq_iff]
        right
        aesop'
        rw [Vector.get_eq_get]
        rw [←Option.some_inj]
        rw [←List.get?_eq_get]
        simp
        have h_aux : (false :: List.replicate n false) = List.replicate n.succ false := by rfl
        rw [h_aux]
        rw [List.get?_replicate h']

lemma oneBitSetVec_congr {n : ℕ} {m m' : Fin n} (h : m.val = m'.val) :
  oneBitSetVec n m = oneBitSetVec n m' := by
  unfold oneBitSetVec
  apply Vector.ext
  intros i
  rw [Vector.get_set_eq_if, Vector.get_set_eq_if]
  rcases m with ⟨m, h⟩
  rcases m' with ⟨m', h'⟩
  rcases i with ⟨i, h''⟩
  simp
  simp at h
  rw [h]
   

theorem Bitvec.toNat_oneBitSetVec_eq_oneBitSet {n : ℕ} {m : Fin n} :
  Bitvec.toNat (oneBitSetVec n m) = oneBitSet (n - m.val - 1) := by
  have h_oneBitSet : oneBitSet (n - m.val - 1) = oneBitSet (n - m.val - 1) % 2 ^ n := by
    rw [Nat.mod_eq_of_lt]
    unfold oneBitSet
    rw [Nat.pow_lt_iff_lt_right (by simp)]
    simp
    apply Nat.lt_of_lt_of_le
    apply Nat.sub_lt
    apply Nat.lt_sub_of_add_lt
    simp
    linarith
    apply Nat.sub_le
  rw [h_oneBitSet]
  rw [←Bitvec.toNat_ofNat]
  rw [@Bitvec.ofNat_oneBitSet_eq_oneBitSetVec n ⟨n - ↑m - (1 : ℕ), by {
    apply Nat.lt_of_lt_of_le
    apply Nat.sub_lt
    apply Nat.lt_sub_of_add_lt
    simp
    linarith
    apply Nat.sub_le
  }⟩]
  simp
  rw [@oneBitSetVec_congr n ⟨n - (n - ↑m - (1 : ℕ)) - (1 : ℕ), _⟩ m (by {
    simp
    rw [←Nat.sub_add_eq n ↑m,
        Nat.sub_sub_self (Nat.succ_le_of_lt m.isLt)]
    simp
  })]




lemma oneSetBit_and {n : ℕ} {m : Fin n} {x : Bitvec n} : 
  (x &&& (oneBitSetVec n m)) = Vector.replicate n false 
    ∨ (x &&& (oneBitSetVec n m)) = oneBitSetVec n m  := by
  generalize eq : Vector.get x m = s
  cases s
  · left
    unfold oneBitSetVec
    apply Vector.ext
    intros i
    dsimp [(· &&& ·), Bitvec.and]
    rw [Vector.get_map₂]
    rw [Vector.get_set_eq_if]
    by_cases eq': i = m
    · subst eq'
      rw [eq]
      simp
    · simp
      right
      tauto
  · right
    apply Vector.ext
    dsimp [(· &&& ·), Bitvec.and, oneBitSetVec]
    intros i
    rw [Vector.get_map₂]
    rw [Vector.get_set_eq_if]
    by_cases eq': i = m
    · subst eq'
      rw [eq]
      simp
    · simp
      aesop

theorem Bitvec.two_bits_set {n : ℕ} {i j : Fin n} (h : i ≠ j) :
  Bitvec.or (oneBitSetVec n i) (oneBitSetVec n j) = Bitvec.ofNat n (oneBitSet (n - i.val - 1) + oneBitSet (n - j.val - 1)) := by
  induction' n with n ih; try aesop
  rw [Bitvec.ofNat_succ]
  apply Vector.ext
  rintro ⟨m, hm⟩ 
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  unfold Bitvec.or
  rw [Vector.get_map₂]
  simp
  symm
  rw [Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get]
  simp
  by_cases eq : m = n
  · subst eq
    rw [List.get?_append_right (by simp)]
    simp
    unfold oneBitSetVec
    by_cases eq' : i = m
    · rw [Vector.get_set_eq_if]
      simp
      subst eq'
      simp
      rw [Nat.succ_sub (by simp)]
      simp
      rw [Nat.succ_sub (Nat.le_of_lt_succ hj)]
      simp
      have hj := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) (by aesop)
      rw [Nat.add_mod]
      rw [@oneBitSet_mod_2 (i - j) (Nat.lt_sub_of_add_lt (by simp[hj]))]
      simp [oneBitSet]
    · rw [Vector.get_set_eq_if,
          Vector.get_replicate]
      simp [eq']
      rw [Vector.get_set_eq_if]
      simp
      by_cases eq'' : j = m
      · subst eq''
        simp
        rw [Nat.succ_sub (Nat.le_of_lt_succ hi)]
        simp
        rw [Nat.succ_sub (by simp)]
        simp
        rw [Nat.add_mod]
        rw [@oneBitSet_mod_2 (j - i) (Nat.lt_sub_of_add_lt (by simp [Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq']))]
        simp [oneBitSet]
      · simp [eq'']
        have h_aux : false ::ᵥ Vector.replicate m false = Vector.replicate m.succ false := by simp
        rw [h_aux, Vector.get_replicate]
        simp
        rw [Nat.succ_sub (Nat.le_of_lt_succ hi)]
        simp
        rw [Nat.succ_sub (Nat.le_of_lt_succ hj)]
        simp
        rw [Nat.add_mod]
        rw [@oneBitSet_mod_2 (m - i) (Nat.lt_sub_of_add_lt (by simp [Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq']))]
        rw [@oneBitSet_mod_2 (m - j) (Nat.lt_sub_of_add_lt (by simp [Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) eq'']))]
        simp
  · rw [List.get?_append (by simp [Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hm) eq])] 
    unfold oneBitSetVec
    rw [Vector.get_set_eq_if, Vector.get_set_eq_if]
    simp
    by_cases eq' : i = m
    · subst eq'
      simp
      simp
      rw [Nat.succ_sub (Nat.le_of_lt_succ hj)]
      simp
      rw [Nat.succ_sub  (Nat.le_of_lt_succ hm)]
      simp 
      by_cases eq'' : j = n
      · subst eq''
        simp
        rw [Nat.add_div (by linarith)]
        have h_oneBit : oneBitSet (0 : ℕ) / (2 : ℕ) = 0 := by simp [oneBitSet]
        rw [h_oneBit]
        simp
        rw [oneBitSet_mod_2 (Nat.lt_sub_of_add_lt (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (by simp [hm])) (by simp[eq])))]
        simp
        generalize eq_i_j : j - i = s
        rcases s with _ | s
        · aesop'
          have hh := Nat.le_antisymm (Nat.le_of_lt_succ hi) eq_i_j
          aesop
        · rw [oneBitSet_div_2]
          rw [@Bitvec.ofNat_oneBitSet_eq_oneBitSetVec j ⟨s, by {
            apply Nat.lt_of_succ_le
            rw [←eq_i_j]
            exact Nat.sub_le _ _
          }⟩]
          simp
          unfold oneBitSetVec
          simp
          rw [List.get?_set,
              List.get?_replicate (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq),
              ←Nat.sub_add_eq,
              Nat.add_one, ←eq_i_j,
              Nat.sub_sub_self (Nat.le_of_lt_succ hi)]
          simp
      · specialize (@ih ⟨i, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq⟩ ⟨j, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) eq''⟩ (by {
          simp at h
          simp [h]
        }))
        have ih := congrArg (Function.swap Vector.get ⟨i, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq⟩) ih
        simp only [Function.swap] at ih
        unfold Bitvec.or at ih
        rw [Vector.get_map₂] at ih
        rw [Vector.get_eq_get, Vector.get_eq_get, Vector.get_eq_get] at ih
        rw [←Option.some_inj] at ih
        rw [←List.get?_eq_get] at ih
        simp at ih
        generalize eq_n_j : n - j = s
        rcases s with _ | s
        · aesop'
          have hh := Nat.le_antisymm (Nat.le_of_lt_succ hj) eq_n_j
          tauto
        · rw [eq_n_j] at ih
          simp at ih
          rw [Nat.add_div (by linarith)]
          rw [oneBitSet_div_2]
          rw [oneBitSet_mod_2 (Nat.lt_sub_of_add_lt (by simp [Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq]))]
          simp
          rw [oneBitSet_mod_2 (by simp)]
          simp
          generalize eq_n_i : n - i = q
          rcases q with _ | q
          · aesop'
            have hh := Nat.le_antisymm (Nat.le_of_lt_succ hi) eq_n_i
            tauto
          · rw [oneBitSet_div_2]
            rw [eq_n_i] at ih
            simp at ih
            rw [←ih]
            simp
            left
            rw [←Option.some_inj]
            rw [←List.get?_eq_get]
            unfold oneBitSetVec
            simp
            rw [List.get?_set, List.get?_replicate (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq)]
            simp
    · simp [eq']
      have h_aux : false ::ᵥ Vector.replicate n false = Vector.replicate n.succ false := rfl
      rw [h_aux, Vector.get_replicate]
      simp
      rw [Nat.succ_sub (Nat.le_of_lt_succ hi)]
      simp
      rw [Nat.succ_sub (Nat.le_of_lt_succ hj)]
      simp
      rw [Nat.add_div (by linarith)]
      by_cases eq'' : n = i
      · subst eq''
        simp
        have hh : oneBitSet 0 / (2 : ℕ) = 0 := by simp
        rw [hh]
        simp at h
        generalize eq_n_j : n - j = s
        rcases s with _ | s
        · have eq_n_j := Nat.le_antisymm (Nat.le_of_sub_eq_zero eq_n_j) (Nat.le_of_lt_succ hj)
          tauto
        · rw [oneBitSet_div_2]
          have hh : oneBitSet 0 % (2 : ℕ) = 1 := by simp
          rw [hh]
          rw [oneBitSet_mod_2 (by simp)]
          simp
          rw [@Bitvec.ofNat_oneBitSet_eq_oneBitSetVec n ⟨s, by {
            apply Nat.lt_of_succ_le
            rw [←eq_n_j]
            exact Nat.sub_le _ _
          }⟩] 
          simp
          unfold oneBitSetVec
          simp
          rw [List.get?_set,
              ←Nat.sub_add_eq,
              Nat.add_one, ←eq_n_j, Nat.sub_sub_self (Nat.le_of_lt_succ hj)]
          by_cases eq'' : j = m
          · subst eq''
            rw [List.get?_replicate (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) eq)]
            simp
          · simp [eq'']
            rw [List.get?_replicate (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hm) eq)]
      · generalize eq''' : n - i = s
        rcases s with _ | s
        · have eq_n_i := Nat.le_antisymm (Nat.le_of_sub_eq_zero eq''') (Nat.le_of_lt_succ hi)
          tauto
        · rw [oneBitSet_div_2]
          rw [oneBitSet_mod_2 (by simp)]
          by_cases eq'''' : n = j
          · subst eq''''
            simp
            have h_ob : oneBitSet (0 : ℕ) / (2 : ℕ) = 0 := by simp
            rw [h_ob]
            simp
            rw [@Bitvec.ofNat_oneBitSet_eq_oneBitSetVec n ⟨s, by {
              apply Nat.lt_of_succ_le
              rw [←eq''']
              exact Nat.sub_le _ _
            }⟩] 
            unfold oneBitSetVec
            simp
            rw [List.get?_set,
                ←Nat.sub_add_eq,
                Nat.add_one,
                ←eq''']
            simp [Ne.symm eq]
            rw [Nat.sub_sub_self (Nat.le_of_lt_succ hi)]
            simp [eq']
            rw [List.get?_replicate (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hm) eq)]
          · generalize eq_n_j : n - j = q
            rcases q with _ | q
            · have eq_n_j := Nat.le_antisymm (Nat.le_of_sub_eq_zero eq_n_j) (Nat.le_of_lt_succ hj)
              tauto
            · rw [oneBitSet_div_2]
              rw [oneBitSet_mod_2 (by simp)]
              simp
              specialize (@ih ⟨i, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) (Ne.symm eq'')⟩ ⟨j, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) (Ne.symm eq'''')⟩ (by {
                simp at h
                simp [h]
              }))
              have ih := congrArg (Function.swap Vector.get ⟨m, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hm) eq⟩) ih
              simp only [Function.swap] at ih
              unfold Bitvec.or at ih
              rw [Vector.get_map₂, Vector.get_eq_get, Vector.get_eq_get, Vector.get_eq_get] at ih
              rw [←Option.some_inj, ←List.get?_eq_get] at ih
              simp at ih
              rw [eq''', eq_n_j] at ih
              simp at ih
              rw [←ih]
              simp
              unfold oneBitSetVec
              simp
              rw [List.get_set]
              simp [eq']
              rw [List.get_set]
              rw [List.get_replicate]

theorem Bitvec.two_bits_set' {n : ℕ} {i j : Fin n} (h : i ≠ j) :
  Bitvec.or (oneBitSetVec n ⟨n - i - 1, by {
    simp
    apply Nat.lt_of_lt_of_le
    apply Nat.sub_lt
    apply Nat.lt_sub_of_add_lt
    simp
    linarith
    apply Nat.sub_le
  }⟩) (oneBitSetVec n ⟨n - j - 1, by {
    simp
    apply Nat.lt_of_lt_of_le
    apply Nat.sub_lt
    apply Nat.lt_sub_of_add_lt
    simp
    linarith
    apply Nat.sub_le
  }⟩) = Bitvec.ofNat n (oneBitSet i + oneBitSet j) := by
  rw [Bitvec.two_bits_set (by {
    simp
    intro contr
    rw [←Nat.sub_add_eq,
        ←Nat.sub_add_eq,
        Nat.add_one,
        Nat.add_one,
        Nat.sub_succ,
        Nat.sub_succ] at contr
    have contr := Nat.pred_inj (by {
      apply Nat.lt_sub_of_add_lt
      simp
    }) (by {
      apply Nat.lt_sub_of_add_lt
      simp
    }) contr
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩ 
    simp at contr
    zify [Nat.le_of_lt hi, Nat.le_of_lt hj] at contr
    have h' : ((↑n - ↑i):ℤ) = -(↑i - ↑n) := by ring_nf
    have h'' : ((↑n - ↑j):ℤ) = -(↑j - ↑n) := by ring_nf
    rw [h', h''] at contr
    rw [neg_inj] at contr
    rw [sub_left_inj] at contr
    simp at h
    simp at contr
    tauto
  })]
  simp
  rcases i with ⟨i, hi⟩ 
  rcases j with ⟨j, hj⟩
  simp 
  have h' : n - (n - i - (1 : ℕ)) - (1 : ℕ) = i := by
    rw [←Nat.sub_add_eq]
    rw [←Nat.sub_add_eq]
    rw [←Nat.sub_sub]
    rw [←Nat.sub_sub]
    rw [←Nat.sub_add_eq]
    rw [Nat.sub_sub n i]
    rw [Nat.add_one]
    rw [Nat.add_one]
    rcases n with _ | n; try aesop
    simp
    rw [Nat.sub_sub_self (Nat.le_of_lt_succ hi)]
  have h'' : n - (n - j - (1 : ℕ)) - (1 : ℕ) = j := by
    rw [←Nat.sub_add_eq]
    rw [←Nat.sub_add_eq]
    rw [←Nat.sub_sub]
    rw [←Nat.sub_sub]
    rw [←Nat.sub_add_eq]
    rw [Nat.sub_sub n j]
    rw [Nat.add_one]
    rw [Nat.add_one]
    rcases n with _ | n; try aesop
    simp
    rw [Nat.sub_sub_self (Nat.le_of_lt_succ hj)]
  simp [h', h'']

theorem Bitvec.or_and_distr_left {n : ℕ} {x y z : Bitvec n}:
  x &&& (Bitvec.or y z) = Bitvec.or (x &&& y) (x &&& z) := by
  dsimp [(· &&& ·), Bitvec.and, Bitvec.or]
  apply Vector.ext
  intro m
  rw [Vector.get_map₂, Vector.get_map₂, Vector.get_map₂, Vector.get_map₂, Vector.get_map₂, Bool.and_or_distrib_left]

@[simp]
theorem Bitvec.or_replicate_zero {n : ℕ} {x : Bitvec n} :
  Bitvec.or (Vector.replicate n false) x = x := by 
  apply Vector.ext
  intro m
  unfold Bitvec.or
  rw [Vector.get_map₂,
      Vector.get_replicate]
  simp           

theorem Bitvec.or_comm {n : ℕ} {x y : Bitvec n} :
  Bitvec.or x y = Bitvec.or y x := by
  apply Vector.ext
  intro m
  unfold Bitvec.or
  rw [Vector.get_map₂, Vector.get_map₂, Bool.or_comm]
  

theorem Bitvec.twoBitSet_and {n : ℕ} {i j : Fin n} {x : Bitvec n} : 
  (x &&& (Bitvec.or (oneBitSetVec n i) (oneBitSetVec n j))) = Vector.replicate n false 
    ∨ (x &&& (Bitvec.or (oneBitSetVec n i) (oneBitSetVec n j))) = oneBitSetVec n i
    ∨ (x &&& (Bitvec.or (oneBitSetVec n i) (oneBitSetVec n j))) = oneBitSetVec n j
    ∨ (x &&& (Bitvec.or (oneBitSetVec n i) (oneBitSetVec n j))) = (Bitvec.or (oneBitSetVec n i) (oneBitSetVec n j))  := by
  rw [Bitvec.or_and_distr_left]
  rcases (@oneSetBit_and _ i x) with h | h; rw [h]
  · rcases (@oneSetBit_and _ j x) with h' | h'; rw [h']
    · aesop
    · right
      right
      left
      simp [h']
  · rcases (@oneSetBit_and _ j x) with h' | h'; rw [h']
    · right
      left
      rw [Bitvec.or_comm]
      simp [h]
    · aesop

lemma sum_of_two_oneBitSet {i j : ℕ} (h : i ≠ j):
  oneBitSet i + oneBitSet j < oneBitSet (max i j + 1) := by
  unfold oneBitSet
  by_cases lt : i < j
  · apply Nat.le_trans
    apply Nat.add_lt_add_right
    apply Nat.pow_lt_pow_of_lt_right
    linarith
    linarith
    rw [Nat.max_eq_right (by linarith)]
    ring_nf
    simp
  · have lt := Nat.lt_of_le_of_ne (Nat.le_of_not_lt lt) (Ne.symm h)
    apply Nat.le_trans
    apply Nat.add_lt_add_left
    apply Nat.pow_lt_pow_of_lt_right
    linarith
    exact lt
    rw [Nat.max_eq_left (by linarith)]
    ring_nf
    simp


theorem Bitvec.toNat_twoBitSetVec_eq_oneBitSet {n : ℕ} {i j : Fin n} (h : i ≠ j):
  Bitvec.toNat (Bitvec.or (oneBitSetVec n i) (oneBitSetVec n j)) = (oneBitSet (n - i.val - 1) + oneBitSet (n - j.val - 1)) := by
  have h' : oneBitSet (n - ↑i - (1 : ℕ)) + oneBitSet (n - ↑j - (1 : ℕ)) = (oneBitSet (n - ↑i - (1 : ℕ)) + oneBitSet (n - ↑j - (1 : ℕ))) % (2 ^ n) := by
    rw [Nat.mod_eq_of_lt (by {
      apply Nat.lt_of_lt_of_le 
      apply sum_of_two_oneBitSet
      · rw [Nat.sub_right_comm n ↑i 1]
        rw [Nat.sub_right_comm n ↑j 1]
        intro contr
        apply h
        rcases n with _ | n
        · rcases i with ⟨i, hi⟩
          aesop
        · rw [Nat.succ_sub_one] at contr
          rcases i with ⟨i, hi⟩
          rcases j with ⟨j, hj⟩ 
          simp
          simp at contr
          zify [Nat.le_of_lt_succ hi, Nat.le_of_lt_succ hj] at contr
          have h' : ((↑n - ↑i):ℤ) = -(↑i - ↑n) := by ring_nf
          have h'' : ((↑n - ↑j):ℤ) = -(↑j - ↑n) := by ring_nf
          rw [h', h''] at contr
          rw [neg_inj] at contr
          rw [sub_left_inj] at contr
          simp at contr
          exact contr
      · apply Nat.pow_le_pow_of_le_right (by linarith)
        apply Nat.add_le_of_le_sub
        · rcases n with _ | n
          · rcases i with ⟨i, hi⟩
            aesop
          · linarith
        · apply max_le
          · rw [Nat.sub_right_comm n ↑i 1]
            rcases n with _ | n; try aesop
            simp
          · rw [Nat.sub_right_comm n ↑j 1]
            rcases n with _ | n; try aesop
            simp
  })]
  rw [h',
      ←Bitvec.toNat_ofNat,
      ←Bitvec.two_bits_set h]

lemma Bitvec.ofNat_succ_allOnes_1 {n : ℕ} (h : 1 ≤ n):
  (Bitvec.ofNat (Nat.succ n) (allOnes 1)) = false ::ᵥ (Bitvec.ofNat n (allOnes 1)) := by
  apply Vector.ext
  rintro ⟨m, hm⟩ 
  rw [Bitvec.allOnes_get]
  rcases m with _ | m
  · simp
    generalize eq : Nat.ble n (0 : ℕ) = s
    cases s; try simp
    rw [Nat.ble_eq] at eq
    aesop
  · simp
    rw [@Vector.get_eq_of_eq_vals _ _ _ _ (Fin.succ ⟨m, Nat.lt_of_succ_lt_succ hm⟩) (by rfl),
        Vector.get_cons_succ,
        ←all_ones_succ,
        Bitvec.allOnes_get]
    simp
    generalize eq : Nat.ble n (Nat.succ m) = s
    generalize eq' : Nat.ble (n - (1 : ℕ)) m = s'
    cases s
    · cases s'; try simp
      rw [Nat.ble_eq] at eq'
      rw [←eq, Nat.ble_eq]
      aesop
    · cases s'
      · rw [Nat.ble_eq] at eq
        symm
        rw [←eq', Nat.ble_eq]
        aesop
      · rfl

@[simp]
theorem Bitvec.toNat_false_cons {n : ℕ} {x : Bitvec n} :
  →ℕ (false ::ᵥ x) = x.toNat := by
  match x with
  | ⟨.nil, _⟩ => aesop
  | ⟨.cons b x, _⟩ => 
    unfold Bitvec.toNat Bitvec.bitsToNat Bitvec.addLsb
    simp

@[simp]
theorem Vector.replicate_zero {a : α} :
  Vector.replicate 0 a = Vector.nil := by simp



-- @[simp]
-- theorem Bitvec.toNat_append_replicate_false {n m: ℕ} {x : Bitvec n} :
--   Bitvec.toNat (Vector.append (Vector.replicate m false) x) = Bitvec.toNat x := by
--   induction' m with m ih
--   · simp
--     unfold Bitvec.toNat Vector.append 
--     rcases x with ⟨x, hx⟩ 
--     simp
--   · simp



theorem Bitvec.ofNat_true_cons {n x: ℕ} (h : x < 2^n):
  true ::ᵥ Bitvec.ofNat n x = Bitvec.ofNat n.succ (2^n + x) := by
  induction' n with n ih generalizing x 
  · unfold Bitvec.ofNat Bitvec.ofNat
    simp at h
    rw [h]
    simp
  · rw [Bitvec.ofNat_succ]
    rw [Bitvec.ofNat_succ]
    rw [Nat.add_div (by linarith)]
    have h' : (2 : ℕ) ^ Nat.succ n / (2 : ℕ)  = 2^n := by
      have h : (2 : ℕ) ^ Nat.succ n / (2 : ℕ) = (2 : ℕ) ^ Nat.succ n / 2^1 := rfl
      rw [h, Nat.pow_div (by linarith) (by linarith)]
      simp
    rw [h']
    have h' : (2 : ℕ) ^ Nat.succ n % (2 : ℕ) + x % (2 : ℕ) = x % 2 := by simp [Nat.pow_succ, Nat.mul_mod]
    rw [h']
    have h' : ¬ (2 : ℕ) ≤ x % (2 : ℕ) := by
      intro contr
      have h := @Nat.mod_lt x 2 (by linarith)
      linarith
    simp [h']
    rw [←ih (by {
      rw [Nat.div_lt_iff_lt_mul (by linarith),
          ←Nat.pow_succ]
      exact h
    })]
    have h' : ((2 : ℕ) ^ Nat.succ n + x) % (2 : ℕ) = x % 2 := by simp [Nat.add_mod, Nat.pow_succ]
    rw [h']
    apply Vector.ext
    rintro ⟨m, hm⟩
    rw [Vector.get_eq_get, Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get, ←List.get?_eq_get]
    simp


@[simp]
theorem Bitvec.toNat_true_cons {n : ℕ} {x : Bitvec n} :
  →ℕ (true ::ᵥ x) = 2^n + x.toNat := by
  have h : 2^n + x.toNat = (2^n + x.toNat) % 2 ^ n.succ := by
    rw [Nat.mod_eq_of_lt]
    rw [Nat.add_comm]
    apply Nat.add_lt_of_lt_sub 
    have h : (2 : ℕ) ^ Nat.succ n - (2 : ℕ) ^ n = 2 ^ n := by
      rw [Nat.pow_succ]
      have h : (2 : ℕ) ^ n * (2 : ℕ) - (2 : ℕ) ^ n = (2 : ℕ) ^ n * (2 : ℕ) - ((2 : ℕ) ^ n) * 1 := by simp
      rw [h, ←Nat.mul_sub_left_distrib] 
      simp 
    rw [h]
    exact Bitvec.toNat_lt x
  rw [h, ←Bitvec.toNat_ofNat, ←Bitvec.ofNat_true_cons (Bitvec.toNat_lt x), Bitvec.ofNat_toNat]

@[simp]
theorem Bitvec.ofNat_nil {x : ℕ}:
  Bitvec.ofNat 0 x = Vector.nil := by simp [Bitvec.ofNat]

lemma Bitvec.lastBit' {x : Bitvec 1} :
  →ℕ (x &&& (Bitvec.ofNat 1 (allOnes 1))) = x.toNat % 2 := by
  rcases x with ⟨x, h⟩
  rcases x with _ | ⟨b, x⟩; try tauto
  rcases x with _ | ⟨b, x⟩
  · rw [Bitvec.ofNat_succ]
    simp [Bitvec.ofNat_nil]
    -- Here Vector.append has been unfolded - see Vector.nil_append defined above
    dsimp [(· &&& ·)]
    unfold Bitvec.and Vector.map₂ Bitvec.toNat bitsToNat addLsb
    simp
    cases b; try aesop
    aesop
  · rw [Bitvec.ofNat_succ]
    simp [Bitvec.ofNat_nil]
    dsimp [(· &&& ·)]
    unfold Bitvec.and Vector.map₂ Bitvec.toNat bitsToNat addLsb
    simp
    cases b; try aesop
    aesop
  

lemma Bitvec.lastBit'' {n : ℕ} {x : Bitvec n} (h : 1 < n):
  Bitvec.toNat (x &&& (Bitvec.ofNat n (allOnes 1))) = x.toNat % 2 := by
  induction x using Vector.inductionOn with
  | h_nil => simp
  | @h_cons n b x ih =>
    have h := Nat.le_of_lt_succ h
    by_cases eq : n = 1
    · subst eq
      rw [Bitvec.ofNat_succ]
      have h' : allOnes (1 : ℕ) / (2 : ℕ) = 0 := by rfl
      rw [h']
      have h' : allOnes (1 : ℕ) % (2 : ℕ) = 1 := by rfl
      rw [h']
      simp
      rw [Bitvec.ofNat_zero_eq_replicate]
      rcases x with ⟨x, hx⟩
      rcases x with _ | ⟨a, x⟩; try tauto
      rcases x with _ | ⟨a, x⟩
      · dsimp [(· &&& ·)]
        unfold Bitvec.toNat Bitvec.and bitsToNat addLsb
        simp
        ring_nf
        simp [Nat.add_mod]
        cases a; try aesop
        aesop
      · simp at hx
    · have h := Nat.lt_of_le_of_ne h (Ne.symm eq)
      rw [Bitvec.ofNat_succ_allOnes_1 (Nat.le_of_lt h)]
      dsimp [(· &&& ·)] at *
      unfold Bitvec.and
      simp only [Vector.map₂_cons, Bool.and_false, toNat_false_cons]
      unfold Bitvec.and at ih
      rw [ih h]
      cases b; try simp
      simp [Nat.add_mod]
      have h' : (2 : ℕ) ^ n % (2 : ℕ) % (2 : ℕ) = 0 := by
        rcases n with _ | n; try aesop
        simp [Nat.pow_succ]
      rw [h']
      simp

theorem Bitvec.lastBit {n : ℕ} {x : Bitvec n} (h : 1 ≤ n): 
  Bitvec.toNat (x &&& (Bitvec.ofNat n (allOnes 1))) = x.toNat % 2 := by
  by_cases eq : 1 = n
  · subst eq
    rw [Bitvec.lastBit']
  · have h := Nat.lt_of_le_of_ne h eq
    rw [Bitvec.lastBit'' h]

@[simp]
theorem Bitvec.toNat_nil :
  →ℕ Vector.nil = 0 := by simp

@[simp]
theorem Bitvec.ushr_nil {m : ℕ} :
  Bitvec.ushr Vector.nil m = Vector.nil := by simp

@[simp]
theorem Bitvec.ushr_cons_false {m n: ℕ} {x : Bitvec n}:
  (false ::ᵥ x) >>> m = false ::ᵥ x >>> m := by
  apply Vector.ext
  rintro ⟨i, hi⟩
  by_cases lt : i < m
  · rw [Bitvec.ushr_alternative₁ (by simp [lt])]
    rcases i with _ | i; try simp
    rw [@Vector.get_eq_of_eq_vals _ _ _ _ (Fin.succ ⟨i, Nat.lt_of_succ_lt_succ hi⟩) (by rfl),
        Vector.get_cons_succ,
        Bitvec.ushr_alternative₁ (by {
          simp
          linarith
        })]
  · have lt := Nat.le_of_not_lt lt
    rw [Bitvec.ushr_alternative₂ (by simp [lt])]
    simp
    rcases i with _ | i; try simp
    simp
    symm
    by_cases eq : m = i.succ
    · subst eq
      simp
      rw [@Vector.get_eq_of_eq_vals _ _ _ _ (Fin.succ ⟨i, Nat.lt_of_succ_lt_succ hi⟩) (by rfl),
        Vector.get_cons_succ,
        Bitvec.ushr_alternative₁ (by simp)]
    · have lt := Nat.lt_of_le_of_ne lt eq
      rw [@Vector.get_eq_of_eq_vals _ _ _ _ (Fin.succ ⟨i, Nat.lt_of_succ_lt_succ hi⟩) (by rfl),
          Vector.get_cons_succ,
          Bitvec.ushr_alternative₂ (by {
            simp
            linarith
          }),
          @Vector.get_eq_of_eq_vals _ _ _ _ (Fin.succ ⟨i - m, by {
            apply Nat.sub_lt_left_of_lt_add (Nat.le_of_lt_succ lt)
            linarith
          }⟩) (by {
            simp
            zify [Nat.le_of_lt_succ lt, Nat.le_of_lt (Nat.lt_of_succ_lt_succ hi), Nat.le_of_lt lt]
            ring_nf
          }),
          Vector.get_cons_succ]
      
@[simp]
theorem Bitvec.toNat_cong {a b : ℕ} {x : Bitvec a} {h : a = b}:
  →ℕ (Bitvec.cong h x) = Bitvec.toNat x := by
  unfold Bitvec.cong Bitvec.toNat
  rcases x with ⟨x, _⟩ 
  simp

@[simp]
theorem Bitvec.toNat_append_full {n m: ℕ} {x : Bitvec n} {y : Bitvec m} :
  →ℕ (Vector.append x y) = 2^m * (→ℕ x) + (→ℕ y) := by
  induction x using Vector.inductionOn generalizing m y with
  | h_nil => 
    simp -- Let's not spend too much time :).
    have h : Vector.append Vector.nil y = Bitvec.cong (by simp) y := by
      apply Vector.ext
      rintro ⟨i, hi⟩
      rw [@Bitvec.get_cong _ _ _ ⟨i, by {
        simp at hi
        tauto
      }⟩ _ (by simp) (by simp)]
      rw [Vector.get_eq_get, Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get, ←List.get?_eq_get]
      simp
    simp [h]
  | @h_cons n b x ih =>
    have h : Vector.append (b ::ᵥ x) y = Bitvec.cong (by linarith) (b ::ᵥ Vector.append x y) := by
      apply Vector.ext
      rintro ⟨i, hi⟩
      rw [@Bitvec.get_cong _ _ _ ⟨i, by {
        simp at hi
        linarith
      }⟩ _ (by linarith) (by simp)]
      rw [Vector.get_eq_get, Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get, ←List.get?_eq_get]
      simp
    simp [h]
    cases b
    · simp
      rw [ih]
    · simp
      rw [ih]
      ring_nf
      simp
  
theorem Bitvec.ushr_eq {n m : ℕ} {x : Bitvec n} (h : m ≤ n) :
  x >>> m = Bitvec.cong (by simp [Nat.add_sub_cancel', h]) (Vector.append (Vector.replicate m false) (Vector.take (n - m) x)) := by
  apply Vector.ext
  rintro ⟨i, hi⟩
  by_cases lt : i < m
  · rw [Bitvec.ushr_alternative₁ (by simp [lt]),
        @Bitvec.get_cong _ _ _ ⟨i, by {
          simp at hi
          simp [Nat.add_sub_cancel', h, hi]
        }⟩ _ (by {
          simp [Nat.add_sub_cancel', h]
        }) (by simp),
        Vector.get_eq_get,
        ←Option.some_inj,
        ←List.get?_eq_get]
    simp
    rw [List.get?_append (by simp [lt]), List.get?_replicate (by simp [lt])] 
  · have lt := Nat.le_of_not_lt lt
    rw [Bitvec.ushr_alternative₂ (by simp [lt]),
        @Bitvec.get_cong _ _ _ ⟨i, by {
          simp at hi
          simp [Nat.add_sub_cancel', h, hi]
        }⟩ _ (by {
          simp [Nat.add_sub_cancel', h]
        }) (by simp),
        Vector.get_eq_get,
        Vector.get_eq_get,
        ←Option.some_inj,
        ←List.get?_eq_get,
        ←List.get?_eq_get]
    simp
    rw [List.get?_append_right (by simp [lt]),
        List.get?_take (by {
          simp
          apply Nat.lt_sub_of_add_lt
          zify [Nat.le_of_lt hi, lt]
          simp [hi]
        })]
    simp

theorem Nat.pow_add (a m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | succ _ ih => rw [Nat.add_succ, Nat.pow_succ, Nat.pow_succ, ih, Nat.mul_assoc]

theorem Bitvec.toNat_take {n m : ℕ} {x : Bitvec n} (h : m < n) : 
  Bitvec.toNat x / (2 : ℕ) ^ m = Bitvec.toNat (Vector.take (n - m) x) := by
  induction x using Vector.inductionOn generalizing m with
  | h_nil => 
    simp at h
  | @h_cons n b x ih =>
    have h' : Vector.take (Nat.succ n - m) (b ::ᵥ x) = Bitvec.cong (by {
      simp
      rw [Nat.succ_sub (by linarith)]
    }) (b ::ᵥ Vector.take (n - m) x) := by
      apply Vector.ext
      rintro ⟨i, hi⟩
      rw [@Bitvec.get_cong _ _ _ ⟨i, by {
          simp at hi
          simp
          rw [Nat.succ_sub (by linarith)] at hi
          exact hi
        }⟩ _ (by {
          simp
          rw [Nat.succ_sub (by linarith)]
        }) (by simp),
        Vector.get_eq_get,
        Vector.get_eq_get,
        ←Option.some_inj,
        ←List.get?_eq_get,
        ←List.get?_eq_get]
      simp
      rw [Nat.succ_sub (by linarith)]
      simp
    rw [h']
    simp
    have h' := Nat.le_of_lt_succ h
    by_cases eq : m = n
    · subst eq
      simp
      have h'' : Vector.take (m - m) x = Bitvec.cong (by simp) Vector.nil := by
        apply Vector.ext
        rintro ⟨i, hi⟩
        simp at hi
      cases b
      · simp
        rw [Nat.div_eq_zero (Bitvec.toNat_lt _), h'']
        simp
      · simp
        rw [Nat.div_eq_zero (Bitvec.toNat_lt _), h'']
        simp
    · have lt := Nat.lt_of_le_of_ne h' eq
      cases b
      · simp
        rw [ih lt]
      · simp
        rw [Nat.add_div (by aesop), ih lt]
        have h_mod : (2 : ℕ) ^ n % (2 : ℕ) ^ m = 0 := by
          have h : n = (n - m + m) := by 
            zify [Nat.le_of_lt lt]
            simp
          rw [h]
          have h : (2 : ℕ) ^ (n - m + m) = (2 : ℕ) ^ (n - m) * (2 : ℕ) ^ m := by
            rw [←Nat.pow_add 2 (n - m) m]  
          rw [h, Nat.mul_mod]
          simp
        rw [h_mod]
        simp
        have h_not : ¬ (2 : ℕ) ^ m ≤ Bitvec.toNat x % (2 : ℕ) ^ m := by
          intro contr
          have contr := Nat.lt_of_le_of_lt contr (Nat.mod_lt _ (by aesop))
          linarith
        simp [h_not]
        rw [Nat.pow_div (Nat.le_of_lt lt) (by linarith)]
      


theorem Bitvec.ushr_toNat {n m : ℕ} {x : Bitvec n} :
  x.toNat / (2 ^ m) = (x >>> m).toNat := by
  by_cases le : m ≤ n
  · rw [Bitvec.ushr_eq le]
    simp
    by_cases eq: m = n
    · subst eq
      have h'' : Vector.take (m - m) x = Bitvec.cong (by simp) Vector.nil := by
        apply Vector.ext
        rintro ⟨i, hi⟩
        simp at hi
      rw [h'']
      simp
      rw [Nat.div_eq_zero (Bitvec.toNat_lt _)]
    · have lt := Nat.lt_of_le_of_ne le eq
      rw [Bitvec.toNat_take lt]
  · have lt := Nat.lt_of_not_le le
    rw [Bitvec.ushr_full_length (Nat.le_of_lt lt)]
    simp
    rw [Nat.div_eq_zero (Nat.lt_trans (Bitvec.toNat_lt _) (Nat.pow_lt_pow_of_lt_right (by linarith) lt))]

theorem Bitvec.ushr_ofNat {n m x: ℕ} (h: x < 2 ^ n) :
  (Bitvec.ofNat n x >>> m) = Bitvec.ofNat n (x / 2 ^ m) := by
  have h' : x = x % (2 ^ n) := by rw [Nat.mod_eq_of_lt h]
  symm
  rw [h', ←Bitvec.toNat_ofNat,
      Bitvec.ushr_toNat,
      Bitvec.ofNat_toNat,
      Bitvec.ofNat_toNat]

theorem Bitvec.allOnes_ushr {n m i : ℕ} (h : i ≤ n) (h' : m ≤ i):
  Bitvec.ofNat n (allOnes i) >>> m = Bitvec.ofNat n (allOnes (i - m)) := by
  rw [Bitvec.ushr_ofNat (by {
    simp [allOnes]
    exact Nat.lt_of_lt_of_le (Nat.sub_lt (by simp) (by linarith)) (Nat.pow_le_pow_of_le_right (by linarith) h)
  })]
  unfold allOnes
  have h'' : (2 : ℕ) ^ i = 2^m * 2^(i-m) := by rw [←Nat.pow_add,
                                                   Nat.add_sub_of_le h']
  rw [h'']
  have h'' : (((2 : ℕ) ^ m * (2 : ℕ) ^ (i - m) - (1 : ℕ)) / (2 : ℕ) ^ m)  = ((2 : ℕ) ^ (i - m) - (1 : ℕ)) := by
    rw [Nat.mul_sub_div 0 (2^m) (2^(i-m)) (by simp)]  
    simp
  rw [h'']

@[simp]
theorem Bitvec.toList_cong {a b : ℕ} {x : Bitvec a} {h : a = b}:
  Vector.toList (Bitvec.cong h x) = Vector.toList x := by
  rcases x with ⟨x, _⟩
  simp [Bitvec.cong]

theorem Bitvec.get_toNat_div {n x : ℕ} {i : Fin n} (h : ↑i.succ < n):
  (Bitvec.ofNat n (x / 2)).get ⟨↑i.succ, h⟩ = (Bitvec.ofNat n x).get i := by
  induction' n with n ih generalizing x
  · simp at h
  · rw [Vector.get_eq_get, Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get, ←List.get?_eq_get]
    rw [Bitvec.ofNat_succ, Bitvec.ofNat_succ]
    simp
    rcases i with ⟨i, hi⟩ 
    by_cases eq : i + 1 = n
    · subst eq
      rw [List.get?_append_right (by simp)]
      simp
      rw [List.get?_append (by simp)]
      simp
      rw [Bitvec.ofNat_succ]
      simp
      rw [List.get?_append_right (by simp)]
      simp
    · simp at h
      have h := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) eq
      simp
      rw [List.get?_append (by simp [h])]
      specialize (@ih (x / 2) ⟨i, by linarith⟩ (by simp [h]))
      rw [Vector.get_eq_get, Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get, ←List.get?_eq_get] at ih
      simp at ih
      rw [ih, List.get?_append (by {
        simp
        linarith
      })]


theorem Bitvec.get_ofNat_succ {n x : ℕ} {i : Fin n} :
  (Bitvec.ofNat n x).get i = (Bitvec.ofNat n.succ x).get (Fin.succ i) := by
  rw [Vector.get_eq_get, Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get, ←List.get?_eq_get]
  simp
  rcases i with ⟨i, hi⟩ 
  simp
  rw [Nat.add_one]
  induction x using Nat.case_strong_induction_on generalizing i n with
  | hz => 
    generalize eq : List.get? (Vector.toList (Bitvec.ofNat (Nat.succ n) (0 : ℕ))) (Nat.succ i) = s
    rw [←@Bitvec.toNat_replicate_false_eq_zero n,
        Bitvec.ofNat_toNat,
        ←eq,
        ←@Bitvec.toNat_replicate_false_eq_zero n.succ,
        Bitvec.ofNat_toNat]
    simp
  | hi x ih =>
    rw [Bitvec.ofNat_succ] 
    simp
    by_cases eq : i.succ = n
    · rw [eq, List.get?_append_right (by simp)]
      simp
      rcases n with _ | n; try tauto
      rw [Bitvec.ofNat_succ]
      simp
      rw [List.get?_append_right (by {
        simp
        aesop
      })]
      simp
      rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt_succ hi)]
      simp
    · rw [List.get?_append (by {
        simp
        exact Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hi) eq
      }),
      ih (x.succ / 2) (by {
        have h := @Nat.div_lt_self x.succ 2 (by linarith) (by linarith)
        exact Nat.le_of_lt_succ h
      }) _
      (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hi) eq),
      Bitvec.ofNat_succ]
      simp
      by_cases eq' : i.succ.succ = n
      · subst eq'
        rw [List.get?_append_right (by {
          simp
        })]
        simp
        rw [Bitvec.ofNat_succ]
        simp
        rw [List.get?_append (by simp),
            Bitvec.ofNat_succ]
        simp
        rw [List.get?_append_right (by simp)]
        simp
      · rw [List.get?_append (by {
          simp
          exact Nat.lt_of_le_of_ne (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hi) eq)) eq'
        })]
        have h_get := @Bitvec.get_toNat_div n (Nat.succ x / 2) ⟨i + 1, (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hi) eq)⟩ (by {
          simp
          exact Nat.lt_of_le_of_ne (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hi) eq)) eq'
        })
        rw [Vector.get_eq_get, Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get, ←List.get?_eq_get] at h_get
        simp at h_get
        rw [h_get]
        have h_get := @Bitvec.get_toNat_div n (Nat.succ x) ⟨i, hi⟩ (by {
          simp
          exact (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hi) eq)
        })
        rw [Vector.get_eq_get, Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get, ←List.get?_eq_get] at h_get
        simp at h_get
        rw [h_get]


theorem Bitvec.drop_ofNat {m n x : ℕ} (h : m ≤ n):
  Bitvec.ofNat m x = Bitvec.cong (by rw [Nat.sub_sub_self h]) (Vector.drop (n - m) (Bitvec.ofNat n x)) := by
    induction' n with n ih generalizing m x
    · simp at h
      subst h
      simp
    · by_cases eq : m = Nat.succ n
      · subst eq
        rw [Bitvec.ofNat_succ]
        apply Vector.ext
        rintro ⟨i, hi⟩
        rw [Vector.get_eq_get, Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get, ←List.get?_eq_get]
        simp
      · have h := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h eq)
        rw [ih h]
        apply Vector.ext
        rintro ⟨i, hi⟩
        rw [Vector.get_eq_get, Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get, ←List.get?_eq_get]
        simp
        rw [List.get?_drop, List.get?_drop, Bitvec.ofNat_succ]
        simp
        by_cases eq' : m = i.succ
        · subst eq'
          simp
          rw [Nat.sub_add_cancel (by linarith),
              List.get?_append_right (by simp)]
          simp
          rcases n with _ | n; try tauto
          simp
          rw [Nat.sub_add_cancel (by linarith), Bitvec.ofNat_succ]
          simp
          rw [List.get?_append_right (by simp)]
          simp
        · rw [List.get?_append (by {
            simp
            have h_le : Nat.succ n - m + i < n.succ := by
              apply Nat.lt_of_lt_of_le
              apply Nat.add_lt_add_left hi
              rw [Nat.sub_add_cancel (by linarith)] 
            have h_le := Nat.le_of_lt_succ h_le
            have h_ne : ¬Nat.succ n - m + i = n := by
              intro contra
              have h' : m ≤ n.succ := by linarith 
              zify [h, h', h_le] at contra
              have h' : (↑n + 1 - ↑m + ↑i : ℤ) = ↑n - (-1 + ↑m - ↑i) := by ring_nf
              rw [h'] at contra
              have h' : (↑n : ℤ) = ↑n - 0 := by ring_nf
              generalize eq : (↑n - (-1 + ↑m - ↑i):ℤ) = s
              rw [eq, h', ←eq, sub_right_inj] at contra
              have h' : (-1 + ↑m - ↑i : ℤ) = ↑m - (↑i + 1) := by ring_nf
              rw [h'] at contra
              have h_0 : (0 : ℤ) = (↑i + 1) - (↑i + 1) := by ring_nf
              rw [h_0, sub_left_inj] at contra
              zify at eq'
              tauto
            exact Nat.lt_of_le_of_ne h_le h_ne
          })]
          have h_get := @Bitvec.get_toNat_div n x ⟨n - m + i, by {
            apply Nat.lt_of_lt_of_le
            apply Nat.add_lt_add_left hi
            rw [Nat.sub_add_cancel (by linarith)]
          }⟩ (by {
            simp
            have h_le : n - m + i + 1 < n.succ := by
              simp
              apply Nat.lt_of_lt_of_le
              rw [Nat.add_assoc]
              apply Nat.add_lt_add_left (by {
                have h := Nat.succ_le_of_lt hi
                exact Nat.lt_of_le_of_ne h (Ne.symm eq')
              })
              rw [Nat.sub_add_cancel (by linarith)] 
              linarith
            have h_le := Nat.le_of_lt_succ h_le
            have h_ne : ¬n - m + i + 1 = n := by
              intro contra
              have h' : m ≤ n.succ := by linarith 
              zify [h, h', h_le] at contra
              have h' : (↑n - ↑m + ↑i + 1 : ℤ) = ↑n - (-1 + ↑m - ↑i) := by ring_nf
              rw [h'] at contra
              have h' : (↑n : ℤ) = ↑n - 0 := by ring_nf
              generalize eq : (↑n - (-1 + ↑m - ↑i):ℤ) = s
              rw [eq, h', ←eq, sub_right_inj] at contra
              have h' : (-1 + ↑m - ↑i : ℤ) = ↑m - (↑i + 1) := by ring_nf
              rw [h'] at contra
              have h_0 : (0 : ℤ) = (↑i + 1) - (↑i + 1) := by ring_nf
              rw [h_0, sub_left_inj] at contra
              zify at eq'
              tauto
            exact Nat.lt_of_le_of_ne h_le h_ne
          })
          rw [Vector.get_eq_get, Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get, ←List.get?_eq_get] at h_get
          simp at h_get
          rw [←h_get]
          have h_eq : (n - m + i + 1) = (Nat.succ n - m + i) := by
            have h' : m ≤ n.succ := by linarith 
            zify [h, h']
            ring_nf
            simp
          rw [h_eq]

theorem Bitvec.drop_ofNat' {m n x : ℕ} (h : m ≤ n):
  (Vector.drop (n - m) (Bitvec.ofNat n x)) = Bitvec.cong (by rw [Nat.sub_sub_self h]) (Bitvec.ofNat m x) := by 
  apply Vector.ext
  rintro ⟨i, hi⟩
  rw [@Bitvec.get_cong _ _ _ ⟨i, by {
          rw [Nat.sub_sub_self h] at hi
          simp [hi]
        }⟩ _ (by rw [Nat.sub_sub_self h]) (by simp)]
  rw [Vector.get_eq_get, Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get, ←List.get?_eq_get]
  simp
  have h' := @Bitvec.drop_ofNat m n x h
  have h' := congrArg (Function.swap Vector.get ⟨i, by {
    rw [Nat.sub_sub_self h] at hi
    exact hi
  }⟩) h' 
  simp [Function.swap] at h'
  rw [Vector.get_eq_get, Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get, ←List.get?_eq_get] at h'
  simp at h'
  rw [←h']

theorem Bitvec.ofNat_and_allOnes {n m : ℕ} {x : Bitvec n} :
  x &&& (Bitvec.ofNat n (allOnes (m : ℕ))) = Bitvec.ofNat n (x.toNat % (2 ^ m)) := by
  by_cases le : m ≤ n
  · rw [←Bitvec.toNat_ofNat,
        @Bitvec.drop_ofNat m n _ le]
    simp
    rw [Bitvec.ofNat_toNat]
    have h : Bitvec.toNat (Vector.drop (n - m) x) = Bitvec.toNat (Vector.append (Vector.replicate (n - m) false) (Vector.drop (n - m) x)) := by simp
    rw [h]
    have h' : n - m + (n - (n - m)) = n := by
      rw [Nat.sub_sub_self le]
      rw [Nat.sub_add_cancel le]
    have h : (Bitvec.toNat (Vector.append (Vector.replicate (n - m) false) (Vector.drop (n - m) x))) = (Bitvec.toNat (Bitvec.cong h' (Vector.append (Vector.replicate (n - m) false) (Vector.drop (n - m) x)))) := by
      symm
      apply @Bitvec.toNat_cong _ n _ _
    rw [h, Bitvec.ofNat_toNat]
    apply Vector.ext
    rintro ⟨i, hi⟩
    rw [Bitvec.and_allOnes_eq_get, Vector.get_eq_get, Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get]
    simp
    by_cases lt : i < n - m
    · simp [lt]
      rw [List.get?_append (by simp[lt]), List.get?_replicate lt]
    · simp [lt]
      rw [←List.get?_eq_get, List.get?_append_right (by {
        simp at lt
        simp [lt]
      })]
      simp
      rw [List.get?_drop,
          Nat.add_comm, 
          Nat.sub_add_cancel (by {
            simp at lt
            simp [lt]
          })]
  · simp at le
    rw [Nat.mod_eq_of_lt (Nat.lt_trans (Bitvec.toNat_lt x) (Nat.pow_lt_pow_of_lt_right (by linarith) le)),
        Bitvec.ofNat_toNat]
    apply Vector.ext
    intro i
    rw [Bitvec.and_allOnes_eq_get, Nat.sub_eq_zero_of_le (Nat.le_of_lt le)]
    simp



theorem Bitvec.toNat_and_allOnes {n m : ℕ} {x : Bitvec n} :
  →ℕ (x &&& (Bitvec.ofNat n (allOnes (m : ℕ)))) = (→ℕ x) % (2 ^ m) := by
  by_cases lt : m < n
  · rw [Bitvec.ofNat_and_allOnes,
        Bitvec.toNat_ofNat,
        Nat.mod_eq_of_lt (by {
          apply Nat.lt_trans
          apply Nat.mod_lt _ (by simp)
          exact Nat.pow_lt_pow_of_lt_right (by linarith) lt
        })]
  · simp at lt
    rw [Bitvec.ofNat_and_allOnes,
        Bitvec.toNat_ofNat,
        Nat.mod_eq_of_lt (by {
          rw [Nat.mod_eq_of_lt]
          apply Nat.lt_of_lt_of_le
          apply Bitvec.toNat_lt
          simp
          apply Nat.lt_of_lt_of_le
          apply Bitvec.toNat_lt
          apply Nat.pow_le_pow_of_le_right (by linarith) lt
        })]
    

theorem Bitvec.and_ofNat_allOnes {n m x : ℕ} (h : x < 2 ^ m) (h' : m ≤ n):
  Bitvec.ofNat n x = (Bitvec.ofNat n x) &&& (Bitvec.ofNat n (allOnes m)) := by
  rw [←Bitvec.ofNat_toNat ((Bitvec.ofNat n x) &&& (Bitvec.ofNat n (allOnes m))), 
      Bitvec.toNat_and_allOnes,
      Bitvec.toNat_ofNat,
      Nat.mod_eq_of_lt (by {
        rw [Nat.mod_eq_of_lt (by {
          apply Nat.lt_of_lt_of_le
          exact h
          exact Nat.pow_le_pow_of_le_right (by linarith) h'
        })]
        exact h
      }),
      Nat.mod_eq_of_lt (by {
        apply Nat.lt_of_lt_of_le
        exact h
        exact Nat.pow_le_pow_of_le_right (by linarith) h'
      })]

