import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.Nat.ModEq
import Mathlib.Init.Data.Nat.Lemmas
import Risc0.Wheels
import Risc0.Bitvec.Lemmas

open Mathlib (Vector) in
@[simp]
def Vector.getElem_eq_getElem {k} {α} {v : Vector α k} {i : Fin k} : v[i] = v.toList[i] := rfl 

open Mathlib (Vector) in
@[simp]
def Vector.getElem_eq_h_getElem {k} {α} {v : Vector α k} {i : ℕ} (hi : i < k) : v[i] = v.toList[i]'(by simp [hi]) := rfl 

open Mathlib (Vector) in
def Bitvec.getElem_eq_getElem {k} {v : Bitvec k} {i : Fin k} : v.toList[i] = v[i] := rfl 

open Mathlib (Vector) in
def Bitvec.getElem_h_eq_getElem {k} {v : Bitvec k} {i : ℕ} (h : i < k) : v.toList[i]'(by simp [h]) = v[i]'h := rfl 

open Mathlib Vector

@[simp]
theorem Vector.map₂_cons (hd₁ : α) (tl₁ : Vector α n) (hd₂ : β) (tl₂ : Vector β n) (f : α → β → γ) :
    Vector.map₂ f (hd₁ ::ᵥ tl₁) (hd₂ ::ᵥ tl₂) = f hd₁ hd₂ ::ᵥ (Vector.map₂ f tl₁ tl₂) :=
  rfl

@[simp]
theorem Vector.get_map₂ (v₁ : Vector α n) (v₂ : Vector β n) (f : α → β → γ) (i : Fin n) :
    (map₂ f v₁ v₂)[i] = f (v₁[i]) (v₂[i]) := by
  clear * - v₁ v₂
  induction v₁, v₂ using inductionOn₂
  case nil =>
    exact Fin.elim0 i
  case cons x xs y ys ih =>
    rw [map₂_cons]
    cases i using Fin.cases <;> aesop'

@[simp]
theorem Vector.get_map₂' (v₁ : Vector α n) (v₂ : Vector β n) (f : α → β → γ) (i : ℕ) (h₀ : i < n) :
    (map₂ f v₁ v₂)[i] = f (v₁[i]) (v₂[i]) := by
  convert Vector.get_map₂ v₁ v₂ f ⟨i, h₀⟩

def allOnes (n : ℕ) : ℕ := 2 ^ n - 1

@[simp]
def allOnes_zero : allOnes 0 = 0 := rfl

@[simp] lemma all_ones_div_two {n : ℕ} : allOnes n.succ / 2 = allOnes n :=
  by unfold allOnes; omega

@[simp] lemma all_ones_succ {n : ℕ} : allOnes n.succ = 2 * (allOnes n) + 1 := by
  unfold allOnes
  have eq₁ : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
  omega

@[simp] lemma all_ones_succ_mod_2 {n : ℕ} :
  allOnes n.succ % 2 = 1 := by try simp [Nat.add_mod]

lemma all_ones_contains_only_ones {n i : ℕ} (h : i < n) :
  (Bitvec.ofNat n (allOnes n)).toList[i]? = some true := by
  induction' n with n ih; try trivial
  unfold Bitvec.ofNat
  simp
  by_cases eq : i = n
  · subst eq
    simp [Nat.add_mod, Nat.mul_mod]
  · have h : i < n := by 
      cases (Nat.lt_or_eq_of_le (Nat.lt_succ.mp h)); try trivial; try aesop
    rw [List.getElem?_append (by simp [h])]
    rw [←all_ones_succ, all_ones_div_two]
    rw [←ih h]

@[simp]
lemma Bitvec.ofNat_zero_get_eq_zero {n i : ℕ} (h : i < n) : 
  (Bitvec.ofNat n 0).toList[i]? = some false := by
  induction' n with n ih; try trivial
  unfold Bitvec.ofNat
  try simp
  by_cases eq : i = n;
  · subst eq
    rw [List.getElem?_append_right (by try simp)]
    try simp
  · have h : i < n := by 
      cases (Nat.lt_or_eq_of_le (Nat.lt_succ.mp h)); try trivial; try aesop
    rw [List.getElem?_append (by try simp [h])]
    rw [←ih h]

lemma allOnes_toList_get?_higher_eq_zero {n m i : ℕ} (h : n ≤ m) (h' : i < m - n) :
  (Bitvec.ofNat m (allOnes n)).toList[i]? = some false := by
  induction' n with n ih generalizing m i
  · try simp [allOnes]
    rw [Bitvec.ofNat_zero_get_eq_zero (by {
      try simp at h'
      exact h'
    })]
  · rcases m with _ | m; try trivial
    try simp at h'
    unfold Bitvec.ofNat
    rw [Vector.toList_append, 
        List.getElem?_append (Nat.lt_of_lt_of_le h' (by aesop)),
        all_ones_div_two,
        ih (Nat.le_of_succ_le_succ h) h']

theorem allOnes_get_higher_eq_zero {n m i : ℕ} (h : n ≤ m) (h' : i < m - n) :
  (Bitvec.ofNat m (allOnes n))[i]'(
    Nat.lt_of_lt_of_le h' (by omega)
  ) = false := by
  unfold GetElem.getElem instGetElemNatLt; dsimp
  rw [Vector.get_eq_get,
      ←Option.some_inj,
      ←List.get?_eq_get]
  simp [allOnes_toList_get?_higher_eq_zero h h']

lemma Bitvec.ofNat_toList_reverse_n_get_eq_ofNat_m_get {x n m i : ℕ} (h : i < n) (h' : n ≤ m) :
  (Bitvec.ofNat n x).toList.reverse[i]?  = (Bitvec.ofNat m x).toList.reverse[i]? := by
  revert n m i
  induction x using Nat.case_strong_induction_on with
  | hz => 
      intros n m i h h'
      rw [List.getElem?_reverse (by try simp [h]), List.getElem?_reverse (by try simp; exact Nat.lt_of_lt_of_le h h')]
      rcases n with _ | n; try trivial
      try simp
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
    try simp
    rcases i with _ | i; try aesop
    try simp
    rw [ih _ (Nat.le_of_lt_succ 
      (Nat.div_lt_self (by linarith) (by try simp))) 
      (Nat.lt_of_succ_lt_succ h)
      (Nat.le_of_succ_le_succ h')]

theorem Bitvec.ofNat_reverse_n_get_eq_ofNat_m_get {x n m i : ℕ} (h : i < n) (h' : n ≤ m) :
  (Bitvec.ofNat n x).reverse[i]'h  = (Bitvec.ofNat m x).reverse[i]'(Nat.lt_of_lt_of_le h h') := by
  unfold GetElem.getElem instGetElemNatLt; dsimp
  rw [Vector.get_eq_get]
  rw [Vector.get_eq_get]
  simp [List.getElem_eq_iff]
  simp [
    Vector.toList_reverse,
    Bitvec.ofNat_toList_reverse_n_get_eq_ofNat_m_get h h'
  ]
  simp [←Vector.toList_reverse]
  have hᵢ: i = ↑(⟨i, by exact (Nat.lt_of_lt_of_le h (by try simp [h']))⟩ : Fin (List.length (Vector.toList (Vector.reverse (Bitvec.ofNat m x))))) := rfl
  conv_lhs => rw [hᵢ]
  rw [←List.getElem_eq_iff]

theorem Bitvec.ofNat_n_toList_get_eq_ofNat_m_get {x n m i : ℕ} (h : i < n) (h' : n ≤ m) :
  (Bitvec.ofNat n x).toList[i]?  = (Bitvec.ofNat m x).toList[(m - n) + i]? := by
  rcases n with n | n; try trivial
  rw [←List.get?_eq_getElem?]
  rw [←List.get?_eq_getElem?]
  have h'' := @Bitvec.ofNat_toList_reverse_n_get_eq_ofNat_m_get x n.succ m (n - i) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by aesop)) h'
  have h_i : (n - (n - i)) = i := by omega
  rw [List.getElem?_reverse (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self n)) (by try simp[h']))] at h''
  simp at h''
  rw [h_i] at h''
  rw [List.get?_eq_getElem?]
  rw [h'',
      List.getElem?_reverse (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by try simp [Nat.lt_of_succ_le h']))]
  try simp
  have h_m_i : m - 1 - (n - i) = m - n.succ + i := by
    rcases m with m | m; try trivial
    try simp
    apply Nat.sub_eq_of_eq_add
    rw [←Nat.add_sub_assoc (Nat.le_of_lt_succ h),
        Nat.add_assoc (m - n),
        Nat.add_comm i n,
        ←Nat.add_assoc (m - n),
        Nat.sub_add_cancel (Nat.le_of_succ_le_succ h'),
        Nat.add_sub_cancel]
  rw [h_m_i]

theorem Bitvec.ofNat_n_get_eq_ofNat_m_get {x n m i : ℕ} (h : i < n) (h' : n ≤ m) :
  (Bitvec.ofNat n x)[i]'h  = (Bitvec.ofNat m x)[(m - n) + i]'(by {
    rcases n with _ | n; try trivial
    rcases m with _ | m; try trivial
    simp at *
    rw [←Nat.sub_add_comm h']
    apply Nat.lt_of_le_of_lt
    apply Nat.sub_le_sub_left (Nat.le_of_lt_succ h)
    simp   
  }) := by
  unfold GetElem.getElem instGetElemNatLt; dsimp
  rw [Vector.get_eq_get,
      Vector.get_eq_get,
      List.get_eq_getElem,
      List.get_eq_getElem,
      ←List.getElem_reverse _ _ 
      (by rcases n with _ | n; try trivial; try simp [Nat.lt_of_le_of_lt (Nat.sub_le n i)]),
      ←List.getElem_reverse (Vector.toList (Bitvec.ofNat m x)) _
      (by {
        rcases n with _ | n; try trivial
        rcases m with _ | m; try trivial
        try simp
        exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by try simp)
      })]
  try simp
  have h_rev := @Bitvec.ofNat_toList_reverse_n_get_eq_ofNat_m_get x n m 
    (n - 1 - i) (by {
      rcases n with _ | n; try trivial
      try simp
      exact Nat.lt_of_le_of_lt (Nat.sub_le n i) (by try simp)
    }) h'
  try simp
  rw [List.getElem_eq_iff]
  try simp
  rw [h_rev]
  have h_n_m : (n - 1 - i) = m - 1 - (m - n + i) := by rw [←Nat.sub_sub,
        Nat.sub_sub m 1,
        Nat.add_comm,
        ←Nat.sub_sub m,
        Nat.sub_sub_self h']
  rw [h_n_m, List.getElem?_eq_getElem]

theorem Bitvec.ofNat_n_get_eq_ofNat_m_get' {x n m : ℕ} {i : Fin n} (h' : n ≤ m) :
  (Bitvec.ofNat n x)[i]  = (Bitvec.ofNat m x)[(m - n) + i]'(by {
    rcases i with ⟨i, h⟩ 
    rcases n with _ | n; try trivial
    rcases m with _ | m; try trivial
    try simp
    try simp at *
    rw [←Nat.sub_add_comm h']
    apply Nat.lt_of_le_of_lt
    apply Nat.sub_le_sub_left (Nat.le_of_lt_succ h)
    try simp   
  }) := by
    rcases i with ⟨i, h⟩
    dsimp
    rw [Bitvec.ofNat_n_get_eq_ofNat_m_get (x := x) (n := n) (i := i) _ h']

lemma Bitvec.allOnes_get' {m n : ℕ} {i : ℕ} (h : i < m) (h' : n ≤ m) : (Bitvec.ofNat m (allOnes n))[i]'h = Nat.ble (m - n) i := by 
  -- rcases i with ⟨i, h⟩; dsimp
  by_cases h_lt : i < m - n
  · rw [allOnes_get_higher_eq_zero h' h_lt]
    generalize eq: Nat.ble (m - n) i = s
    cases s; try aesop
    rw [Nat.ble_eq] at eq
    have h'' := Nat.lt_of_le_of_lt eq h_lt
    aesop
  · rw [Nat.not_lt] at h_lt
    simp [getElem_h_eq_getElem]
    rw [←Option.some_inj]
    rw [←List.getElem?_eq_getElem]
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

lemma Bitvec.allOnes_get {m n : ℕ} {i : ℕ} (hi : i < m) : (Bitvec.ofNat m (allOnes n))[i] = Nat.ble (m - n) i := by
  by_cases h' : n ≤ m
  · rw [Bitvec.allOnes_get' _ h']
  · try simp at h' 
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt h')]
    have h : 0 ≤ (↑i : ℕ) := by try simp
    rw [←Nat.ble_eq] at h
    rw [h]
    rw [Bitvec.ofNat_n_get_eq_ofNat_m_get hi (Nat.le_of_lt h')]
    rw [Bitvec.allOnes_get' _ (Nat.le_refl _)]
    try simp

theorem Bitvec.and_allOnes_eq_get' {n m : ℕ} {x : Bitvec m} {i : Fin m} (h : n ≤ m): 
  (Bitvec.and x (Bitvec.ofNat m (allOnes n))).get i = if i < m - n then false else x.get i := by
  rcases i with ⟨i, h'⟩ 
  unfold Bitvec.and
  simp
  rw [Vector.get_eq_get]
  rw [Vector.get_eq_get]
  simp
  rw [getElem_h_eq_getElem]
  rw [getElem_h_eq_getElem]
  rw [Bitvec.allOnes_get']
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
    omega
  all_goals omega

theorem Bitvec.and_allOnes_eq_get {n m : ℕ} {x : Bitvec m} {i : Fin m}: 
  (Bitvec.and x (Bitvec.ofNat m (allOnes n))).get i = if i < m - n then false else x.get i := by
  by_cases h : n ≤ m
  · rw [Bitvec.and_allOnes_eq_get' h]
  · unfold Bitvec.and
    try simp
    rw [Vector.get_eq_get]
    rw [Vector.get_eq_get]
    simp
    rcases i with ⟨i, hi⟩; dsimp
    rw [getElem_h_eq_getElem]
    rw [getElem_h_eq_getElem]
    rw [Bitvec.allOnes_get]
    try simp at h
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt h)]
    -- try simp
    have h : 0 ≤ (↑i : ℕ) := by try simp
    rw [←Nat.ble_eq] at h
    rw [h]
    try simp
    assumption
    assumption


theorem List.get?_eq_of_eq_vals {l : List α} {i j : Fin (l.length)} :  
  i.val = j.val → l.get i = l.get j := by
  intros eq
  rcases i with ⟨i, h⟩
  rcases j with ⟨j, h'⟩
  try simp at eq
  rcases l with x | ⟨x, l⟩; try trivial
  try simp
  rcases i with _ | i; try aesop
  rcases j with _ | j; try aesop
  try simp
  aesop
  
theorem Vector.get_eq_of_eq_vals {n : ℕ} {v : Vector α n} {i j : Fin n} :  
  i.val = j.val → v.get i = v.get j := by
  intros eq
  rw [Vector.get_eq_get,
      Vector.get_eq_get,
      List.get?_eq_of_eq_vals]
  try simp [eq]

theorem Bitvec.get_cong {n m : ℕ} {x : Bitvec n} {i : Fin n} {j : Fin m} (h : n = m) (h' : i.val = j.val) :
  (x.cong h).get j = x.get i := by 
  unfold Bitvec.cong
  rw [Vector.get_eq_get]
  rw [Vector.get_eq_get]
  rcases x with ⟨x, h⟩
  try simp
  apply List.get?_eq_of_eq_vals
  try simp [h']

lemma Option.map₂_map {f : α → β → γ} {x : Option α} {y : Option β}: 
  Option.map₂ f x y =
    Option.bind (Option.map f x) fun g => Option.map g y := by 
  unfold map₂ Option.bind
  aesop


theorem List.get?_replicate {α : Type u_1} {a : α} {n : Nat} {m : ℕ} (h : m < n) :
  List.get? (List.replicate n a) m = some a := by
  rw [List.get?_eq_get (by try simp [h])]
  try simp

theorem Bitvec.ushr_alternative₀ {n m : ℕ} {x : Bitvec n} (h : n ≤ m) (i : Fin n) :
  (x.ushr m)[i] = false := by
  simp [Vector.get_eq_get]
  unfold ushr shiftRightFill
  rw [Vector.congr]
  split
  aesop (config := {warnOnNonterminal := false})
  have : l = ((replicate (min n m) false).append (take (n - m) x)).toList := by aesop
  simp [this]
  have : List.take (n - m) (toList x) = [] := have : n - m = 0 := by omega
                                              by aesop
  simp [this, replicate]

theorem Bitvec.ushr_alternative₀' {n m : ℕ} {x : Bitvec n} (h : n ≤ m) (i : ℕ) (h₀ : i < n) :
  (x.ushr m)[i] = false := by
  simp [Vector.get_eq_get]
  unfold ushr shiftRightFill
  rw [Vector.congr]
  split
  aesop (config := {warnOnNonterminal := false})
  have : l = ((replicate (min n m) false).append (take (n - m) x)).toList := by aesop
  simp [this]
  have : List.take (n - m) (toList x) = [] := have : n - m = 0 := by omega
                                              by aesop
  simp [this, replicate]

theorem Bitvec.ushr_full_length {n m : ℕ} {x : Bitvec n} (h : n ≤ m) :
  x.ushr m = Vector.replicate n false := by
  ext i
  simp
  apply ushr_alternative₀; assumption

theorem Bitvec.ushr_alternative₁ {n m : ℕ} {x : Bitvec n} {i : Fin n} (h : i < m) :
  (x.ushr m)[i] = false := by
  by_cases le : n ≤ m
  · rw [Bitvec.ushr_alternative₀ le]
  · have h_lt : m < n := by omega
    -- have : min n m = m := by rw [min_eq_right (le_of_lt h_lt)]
    rw [Vector.getElem_eq_getElem]
    unfold ushr shiftRightFill
    rw [Vector.congr]
    split
    aesop'
    have : l = ((replicate (min n m) false).append (take (n - m) x)).toList := by aesop
    simp [this, replicate]
    rw [List.getElem_append_left]
    have h₁ : min n m = m := by rw [min_eq_right (le_of_lt h_lt)]
    simp [h₁]
    have h₁ : min n m = m := by rw [min_eq_right (le_of_lt h_lt)]
    rw [h₁]
    simp
    assumption

theorem Bitvec.ushr_alternative₁' {n m : ℕ} {x : Bitvec n} {i : ℕ} (h₀ : i < n) (h : i < m) :
  (x.ushr m)[i] = false := by
  by_cases le : n ≤ m
  · rw [Bitvec.ushr_alternative₀' le]
  · have h_lt : m < n := by omega
    rw [Vector.getElem_eq_h_getElem]
    unfold ushr shiftRightFill
    rw [Vector.congr]
    split
    aesop'
    have : l = ((replicate (min n m) false).append (take (n - m) x)).toList := by aesop
    simp [this, replicate]
    rw [List.getElem_append_left]
    have h₁ : min n m = m := by rw [min_eq_right (le_of_lt h_lt)]
    simp [h₁]
    have h₁ : min n m = m := by rw [min_eq_right (le_of_lt h_lt)]
    rw [h₁]
    simp
    assumption

theorem Bitvec.ushr_alternative₂ {n m : ℕ} {x : Bitvec n} {i : Fin n} (h : m ≤ i) :
  (x.ushr m)[i] = x[i - m]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) (i.isLt)) := by
  by_cases le : n ≤ m
  · rcases i with ⟨i, h_i⟩
    try simp at *
    linarith
  · have h_lt := Nat.lt_of_not_le le
    rw [Vector.getElem_eq_getElem]
    unfold ushr shiftRightFill
    rw [Vector.congr]
    split
    aesop'
    have : l = ((replicate (min n m) false).append (take (n - m) x)).toList := by aesop
    simp [this, replicate]
    rw [List.getElem_append_right]
    simp
    have : min n m = m := min_eq_right (le_of_lt h_lt)
    simp [this]
    rw [←List.getElem_take]
    omega
    simpa
    simp
    omega

theorem Bitvec.ushr_alternative₂' {n m : ℕ} {x : Bitvec n} {i : ℕ} (h₀ : i < n) (h : m ≤ i) :
  (x.ushr m)[i] = x[i - m]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) h₀) := by
  convert ushr_alternative₂ (i := ⟨i, h₀⟩) h

@[simp]
theorem Bitvec.ushr_zero {n : ℕ} {x : Bitvec n} : 
  x.ushr 0 = x := by
  unfold ushr shiftRightFill
  rw [Vector.congr]
  split
  aesop'
  apply Vector.ext
  rintro ⟨m, h⟩ 
  rw [Vector.get_eq_get]
  rw [Vector.get_eq_get]
  simp
  convert rfl
  have : l = ((replicate (min n 0) false).append (take n x)).toList := by aesop
  simp [this]
  rw [min_eq_right (Nat.zero_le _)] at *
  simp at *
  have : (toList x).length = n := by simp [←h]
  simp only [←this]
  rw [List.take_length]

set_option linter.unnecessarySimpa false in
theorem Bitvec.ushr_and_commute {n m : ℕ} {x y : Bitvec n} : 
  (Bitvec.and x y).ushr m = Bitvec.and (x.ushr m) (y.ushr m) := by
  ext i
  rw [Vector.get_eq_get]
  rw [Vector.get_eq_get]
  dsimp
  by_cases lt : i < m
  · unfold Bitvec.and
    rw [←getElem_eq_h_getElem i.2]
    rw [←getElem_eq_h_getElem i.2]
    rw [Bitvec.ushr_alternative₁']
    rw [Vector.get_map₂' _ _ _ _ i.2]
    rw [Bitvec.ushr_alternative₁' (by simp[lt])]
    all_goals simpa
  · have lt := Nat.le_of_not_lt lt
    rw [←getElem_eq_h_getElem i.2]
    rw [Bitvec.ushr_alternative₂']
    unfold Bitvec.and
    rw [←getElem_eq_h_getElem i.2]
    rw [Vector.get_map₂' _ _ _ _ i.2,
        Vector.get_map₂',
        Bitvec.ushr_alternative₂' (by try simp[lt]),
        Bitvec.ushr_alternative₂' (by try simp[lt])]
    all_goals simpa

-- lemma List.list_get! [Inhabited α] {n : ℕ} {l : List α} {j : ℕ} (h : j < n) : 
--   n = l.length → l[j]? = some (l[j]?) := by
--   induction n generalizing j l with
--     | zero => aesop'
--     | succ k _ => intros h₁
--                   rcases l <;> rcases j <;> aesop'

-- theorem List.get!_eq_get? [Inhabited α] {l : List α} {j : ℕ} (h : j < l.length) : 
--   l[j]? = some (l[j]?) := by rw [list_get! h]; try rfl

lemma ble_eq_false {a b : ℕ} : Nat.ble a b = false ↔ b < a := by
  apply Iff.intro <;> intros h
  by_contra contra
  simp at contra
  rw [←Nat.ble_eq] at contra
  aesop
  by_contra contra
  simp at contra
  omega

theorem Bitvec.allOnes_eq_cons {n m : ℕ} (h : n ≤ m):
  Bitvec.ofNat m.succ (allOnes n) = false ::ᵥ Bitvec.ofNat m (allOnes n) := by
  apply Vector.ext
  rintro ⟨i, h'⟩
  rw [Vector.get_eq_get]
  rw [Vector.get_eq_get]
  simp
  rw [Bitvec.getElem_h_eq_getElem, Bitvec.allOnes_get]
  rcases i with _ | i
  · try simp
    generalize eq : Nat.ble (Nat.succ m - n) 0 = s
    cases s; try trivial
    rw [Nat.ble_eq, Nat.le_zero_eq] at eq
    have eq := Nat.le_of_sub_eq_zero eq
    linarith
  · simp
    rw [Bitvec.getElem_h_eq_getElem (h := by omega)]
    rw [allOnes_get]
    generalize eq₁ : (m + 1 - n).ble (i + 1) = b₁
    generalize eq₂ : (m - n).ble i = b₂
    rcases b₁ with _ | _ <;> rcases b₂ with _ | _ <;> try { aesop }
    rw [ble_eq_false] at eq₁
    rw [Nat.ble_eq] at eq₂
    omega
    rw [Nat.ble_eq] at eq₁
    rw [ble_eq_false] at eq₂
    omega
  exact h'

theorem Bitvec.and_comm {n : ℕ} {x y : Bitvec n} :
  Bitvec.and x y = Bitvec.and y x := by
  unfold Bitvec.and
  apply Vector.ext
  rintro ⟨m, h⟩
  simp [Vector.get_eq_get]
  rw [Bitvec.getElem_h_eq_getElem]
  rw [Bitvec.getElem_h_eq_getElem]
  rw [Vector.get_map₂', Vector.get_map₂', Bool.and_comm]
  exact h

theorem Bitvec.and_assoc {n : ℕ} {x y z : Bitvec n} : 
  Bitvec.and (Bitvec.and x y) z = Bitvec.and x (Bitvec.and y z) := by
  unfold Bitvec.and 
  apply Vector.ext
  rintro ⟨m, h⟩
  simp [Vector.get_eq_get]
  rw [Bitvec.getElem_h_eq_getElem]
  rw [Bitvec.getElem_h_eq_getElem]
  rw [Vector.get_map₂', Vector.get_map₂', Vector.get_map₂', Vector.get_map₂', Bool.and_assoc]
  exact h

@[ simp]
theorem Vector.replicate_succ (val : α) :
    replicate (n+1) val = val ::ᵥ (replicate n val) :=
  rfl

@[ simp]
theorem Vector.toList_replicate (val : α) :
  (replicate n val).toList = List.replicate n val := by rfl

theorem Bitvec.ofNat_zero_eq_replicate {n : ℕ} :
  Bitvec.ofNat n 0 = Vector.replicate n false := by
  induction n using Nat.case_strong_induction_on with
  | hz => aesop
  | hi x ih => 
    rw [Bitvec.ofNat_succ]
    try simp
    rw [ih x (Nat.le_refl x)]
    apply Vector.ext
    rintro ⟨m, h⟩
    rw [Vector.get_eq_get, Vector.get_eq_get]
    rw [←Option.some_inj]
    rw [←List.get?_eq_get, ←List.get?_eq_get]
    try simp
    by_cases eq : m = x
    · subst eq
      rw [List.getElem?_append_right (by try simp)]
      try simp
      have h_aux : (false :: List.replicate m false) = List.replicate m.succ false := by rfl
      simp [h_aux]
    · have h := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) eq
      rw [List.getElem?_append (by try simp[h])]
      have h_aux : (false :: List.replicate x false) = List.replicate x.succ false := by rfl
      rw [h_aux]
      rw [List.getElem?_replicate]
      aesop'

@[ simp]
theorem Bitvec.toNat_replicate_false_eq_zero {n : ℕ}  :
  Bitvec.toNat (Vector.replicate n false) = 0 := by
  rw [←Bitvec.ofNat_zero_eq_replicate,
      Bitvec.toNat_ofNat]
  try simp

@[ simp]
theorem Bitvec.replicate_zero_and_x_eq_replicate_zero {n : ℕ} {x : Bitvec n} :
  Bitvec.and (Vector.replicate n false) x = Vector.replicate n false := by
  unfold Bitvec.and
  apply Vector.ext
  intros m
  try simp [Vector.get_map₂, Vector.get_replicate]

theorem Bitvec.eq_zero_of_toNat_eq_zero {n : ℕ} {x : Bitvec n} (h: x.toNat = 0):
  x = Vector.replicate n false := by 
  rw [←Bitvec.ofNat_toNat x,
      h,
      Bitvec.ofNat_zero_eq_replicate]

def oneBitSet (n : ℕ) := 2 ^ n

lemma oneBitSet_mod_2 {n : ℕ} (h : 0 < n):
  oneBitSet n % 2 = 0 := by
  cases n; try aesop
  try simp [oneBitSet, Nat.pow_succ, Nat.mul_mod]

@[simp]
lemma oneBitSet_zero :
  oneBitSet 0 = 1 := rfl

lemma oneBitSet_div_2 {n : ℕ}:
  oneBitSet n.succ / 2 = oneBitSet n := by try simp [oneBitSet, Nat.pow_succ]

def oneBitSetVec (n : ℕ) (m : Fin n) : Bitvec n := Vector.set (Vector.replicate n false) m true

theorem Bitvec.ofNat_oneBitSet_eq_oneBitSetVec {n : ℕ} {m : Fin n} :
  Bitvec.ofNat n (oneBitSet m.val) = oneBitSetVec n ⟨n - m.val - 1, by {
    try simp
    apply Nat.lt_of_lt_of_le
    apply Nat.sub_lt
    apply Nat.lt_sub_of_add_lt
    try simp
    linarith
    apply Nat.sub_le
  }⟩ := by
  induction' n with n ih; simp; rcases m; omega
  rw [Bitvec.ofNat_succ]
  apply Vector.ext
  rintro ⟨i, h'⟩  
  unfold oneBitSetVec
  rw [Vector.get_set_eq_if]
  rcases m with ⟨m, h⟩
  try simp
  rcases m with _ | m
  · try simp [oneBitSet]
    -- have h_eq : (1 : ℕ) / (2 : ℕ) = 0 := by try simp
    -- rw [h_eq]
    rw [Bitvec.ofNat_zero_eq_replicate]
    rw [Vector.get_eq_get]
    rw [←Option.some_inj]
    rw [←List.get?_eq_get]
    simp
    by_cases eq: n = i
    · subst eq
      try simp
    · rw [List.getElem?_append (by {
        try simp
        exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h') (by aesop)
      })]
      rw [List.getElem?_replicate]
      aesop'
      omega
      try simp
      symm 
      rw [Vector.get_eq_get]
      simp
      have h_aux : (false :: List.replicate n false) = List.replicate n.succ false := by rfl
      simp [h_aux]
  · rw [oneBitSet_div_2,
        oneBitSet_mod_2 (by linarith)]
    try simp
    rw [Vector.get_eq_get]
    rw [←Option.some_inj]
    rw [←List.get?_eq_get]
    try simp
    rw [@ih ⟨m, by linarith⟩]
    try simp
    unfold oneBitSetVec
    try simp
    by_cases eq: i = n - m - 1
    · subst eq
      try simp
      rw [List.getElem?_append (by {
        try simp
        apply Nat.lt_of_lt_of_le
        apply Nat.sub_lt
        apply Nat.lt_sub_of_add_lt
        try simp
        linarith
        linarith
        apply Nat.sub_le
      })]
      rw [List.getElem?_set]
      try simp
      omega
    · by_cases eq' : i = n
      · subst eq'
        try simp
        rw [Vector.get_eq_get]; simp
        have h_aux : (false :: List.replicate i false) = List.replicate i.succ false := by rfl
        simp [h_aux]
        omega
      · rw [List.getElem?_append (by {
          try simp
          try simp
          exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h') (by aesop)
        })]
        rw [Vector.get_eq_get]
        simp
        have h_aux : (false :: List.replicate n false) = List.replicate n.succ false := by rfl
        simp [h_aux]

        rw [List.getElem?_set_ne (by aesop)]
        rw [List.getElem?_replicate]
        try simp
        omega

lemma oneBitSetVec_congr {n : ℕ} {m m' : Fin n} (h : m.val = m'.val) :
  oneBitSetVec n m = oneBitSetVec n m' := by
  unfold oneBitSetVec
  apply Vector.ext
  intros i
  rw [Vector.get_set_eq_if, Vector.get_set_eq_if]
  rcases m with ⟨m, h⟩
  rcases m' with ⟨m', h'⟩
  rcases i with ⟨i, h''⟩
  try simp
  try simp at h
  rw [h]
   

theorem Bitvec.toNat_oneBitSetVec_eq_oneBitSet {n : ℕ} {m : Fin n} :
  Bitvec.toNat (oneBitSetVec n m) = oneBitSet (n - m.val - 1) := by
  have h_oneBitSet : oneBitSet (n - m.val - 1) = oneBitSet (n - m.val - 1) % 2 ^ n := by
    rw [Nat.mod_eq_of_lt]
    unfold oneBitSet
    rw [pow_lt_pow_iff_right (by try simp)]
    try simp
    apply Nat.lt_of_lt_of_le
    apply Nat.sub_lt
    apply Nat.lt_sub_of_add_lt
    try simp
    linarith
    apply Nat.sub_le
  rw [h_oneBitSet]
  rw [←Bitvec.toNat_ofNat]
  rw [@Bitvec.ofNat_oneBitSet_eq_oneBitSetVec n ⟨n - ↑m - (1 : ℕ), by {
    apply Nat.lt_of_lt_of_le
    apply Nat.sub_lt
    apply Nat.lt_sub_of_add_lt
    try simp
    linarith
    apply Nat.sub_le
  }⟩]
  try simp
  rw [@oneBitSetVec_congr n ⟨n - (n - ↑m - (1 : ℕ)) - (1 : ℕ), _⟩ m (by {
    try simp
    rw [←Nat.sub_add_eq n ↑m,
        Nat.sub_sub_self (Nat.succ_le_of_lt m.isLt)]
    try simp
  })]

lemma oneSetBit_and {n : ℕ} {m : Fin n} {x : Bitvec n} : 
  (Bitvec.and x (oneBitSetVec n m)) = Vector.replicate n false 
    ∨ (Bitvec.and x (oneBitSetVec n m)) = oneBitSetVec n m  := by
  generalize eq : Vector.get x m = s
  cases s
  · left
    unfold oneBitSetVec
    ext i
    unfold Bitvec.and
    rw [Vector.get_eq_get]
    rw [Vector.get_eq_get]
    simp
    rw [Bitvec.getElem_h_eq_getElem i.2]
    rw [Vector.get_map₂']
    simp
    intros h
    rw [List.getElem_set]
    simp
    intros contra
    simp [Vector.get_eq_get] at eq
    rw [Bool.eq_false_iff] at eq
    simp [contra] at eq
    rw [Bool.eq_false_iff] at eq
    contradiction
  · right
    apply Vector.ext
    unfold oneBitSetVec Bitvec.and
    intros i
    rw [Vector.get_eq_get]
    rw [Vector.get_eq_get]
    simp
    rw [Bitvec.getElem_h_eq_getElem i.2]
    rw [Vector.get_map₂']
    rcases i with ⟨i, hi⟩
    dsimp at *
    
    simp [Vector.get_eq_get] at eq
    rw [List.getElem_set]
    simp
    rw [List.getElem_set]
    simp
    intros h
    subst h
    exact eq

theorem Bitvec.two_bits_set_aux₁ (n : ℕ)
  (ih :
    ∀ {i j : Fin n},
      i ≠ j →
        (oneBitSetVec n i).or (oneBitSetVec n j) = Bitvec.ofNat n (oneBitSet (n - ↑i - 1) + oneBitSet (n - ↑j - 1)))
  (m : ℕ) (hm : m < n + 1) (i : ℕ) (hi : i < n + 1) (j : ℕ) (hj : j < n + 1) (h : i ≠ j) (eq : ¬m = n)
  (eq' : ¬i = m) :
  (toList (Bitvec.ofNat n ((oneBitSet (n + 1 - i - 1) + oneBitSet (n + 1 - j - 1)) / 2)))[m]? =
    some
      (decide (i = m) || (false :: List.replicate n false)[m]'(by simp; exact hm) ||
        (decide (j = m) || (false :: List.replicate n false)[m]'(by simp; exact hm))) := by
  try simp [eq']
  have h_aux : false :: List.replicate n false = List.replicate n.succ false := rfl
  simp [h_aux, Vector.get_replicate]
  try simp
  rw [Nat.succ_sub (Nat.le_of_lt_succ hi)]
  try simp
  rw [Nat.succ_sub (Nat.le_of_lt_succ hj)]
  try simp
  rw [Nat.add_div (by linarith)]
  by_cases eq'' : n = i
  · subst eq''
    try simp
    try simp at h
    generalize eq_n_j : n - j = s
    rcases s with _ | s
    · have eq_n_j := Nat.le_antisymm (Nat.le_of_sub_eq_zero eq_n_j) (Nat.le_of_lt_succ hj)
      tauto
    · rw [oneBitSet_div_2]
      rw [oneBitSet_mod_2 (by try simp)]
      try simp
      rw [@Bitvec.ofNat_oneBitSet_eq_oneBitSetVec n ⟨s, by {
        apply Nat.lt_of_succ_le
        rw [Nat.succ_eq_add_one]
        rw [←eq_n_j]
        exact Nat.sub_le _ _
      }⟩] 
      try simp
      unfold oneBitSetVec
      simp [List.getElem?_set]
      by_cases eq'' : j = m
      · subst eq''
        have : n - s - 1 = j := by
          rw [Nat.sub_sub]
          rw [Nat.sub_eq_iff_eq_add (by omega)]
          rw [←eq_n_j]
          rw [Nat.add_sub_cancel']
          omega
        simp [if_pos this]
        omega
      · try simp [eq'']
        rw [if_neg]
        rw [List.getElem?_replicate]
        rw [if_pos (by omega)]
        omega
  · generalize eq''' : n - i = s
    rcases s with _ | s
    · have eq_n_i := Nat.le_antisymm (Nat.le_of_sub_eq_zero eq''') (Nat.le_of_lt_succ hi)
      tauto
    · rw [oneBitSet_div_2]
      rw [oneBitSet_mod_2 (by try simp)]
      by_cases eq'''' : n = j
      · subst eq''''
        try simp
        rw [@Bitvec.ofNat_oneBitSet_eq_oneBitSetVec n ⟨s, by {
          apply Nat.lt_of_succ_le
          rw [Nat.succ_eq_add_one]
          rw [←eq''']
          exact Nat.sub_le _ _
        }⟩] 
        unfold oneBitSetVec
        try simp

        rw [List.getElem?_set]
        have : n - s - 1 = i := by omega
        rw [this]
        simp
        rw [if_neg eq']
        rw [List.getElem?_replicate]
        rw [if_pos (by omega)]
        aesop
      · generalize eq_n_j : n - j = q
        rcases q with _ | q
        · have eq_n_j := Nat.le_antisymm (Nat.le_of_sub_eq_zero eq_n_j) (Nat.le_of_lt_succ hj)
          tauto
        · rw [oneBitSet_div_2]
          rw [oneBitSet_mod_2 (by try simp)]
          try simp
          specialize (@ih ⟨i, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) (Ne.symm eq'')⟩ ⟨j, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) (Ne.symm eq'''')⟩ (by {
            try simp at h
            try simp [h]
          }))
          have ih := congrArg (Function.swap Vector.get ⟨m, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hm) eq⟩) ih
          try try simp only [Function.swap] at ih
          unfold Bitvec.or at ih
          simp at ih
          rw [Vector.get_eq_get] at ih
          rw [Vector.get_eq_get] at ih
          rw [Vector.get_eq_get] at ih
          simp at ih
          rw [Bitvec.getElem_h_eq_getElem (by omega)] at ih
          rw [Bitvec.getElem_h_eq_getElem (by omega)] at ih
          rw [Bitvec.getElem_h_eq_getElem (by omega)] at ih
          rw [←Option.some_inj, List.getElem?_eq_getElem]
          apply congr_arg
          apply congr_arg
          rw [Bitvec.getElem_h_eq_getElem (by omega)]
          simp only [eq''', eq_n_j] at ih
          have g₁ : s + 1 - 1 = s := by omega
          have g₂ : q + 1 - 1 = q := by omega
          simp only [g₁, g₂] at ih
          rw [←ih]
          unfold oneBitSetVec
          simp
          rw [List.getElem_set]
          rw [List.getElem_set]
          rw [if_neg eq']
          simp

theorem Bitvec.two_bits_set {n : ℕ} {i j : Fin n} (h : i ≠ j) :
  Bitvec.or (oneBitSetVec n i) (oneBitSetVec n j) = Bitvec.ofNat n (oneBitSet (n - i.val - 1) + oneBitSet (n - j.val - 1)) := by
  induction' n with n ih; try aesop
  rw [Bitvec.ofNat_succ]
  apply Vector.ext
  rintro ⟨m, hm⟩ 
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  unfold Bitvec.or
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
  rw [Vector.get_eq_get]
  rw [Vector.get_eq_get]
  simp
  rw [Bitvec.getElem_h_eq_getElem hm]
  -- rw [Bitvec.getElem_h_eq_getElem hm]
  rw [Vector.get_map₂']
  try simp
  symm
  rw [Bitvec.getElem_h_eq_getElem hm]
  rw [Bitvec.getElem_h_eq_getElem hm]
  rw [←Option.some_inj, ←List.getElem?_eq_getElem]
  try simp
  by_cases eq : m = n
  · subst eq
    rw [List.getElem?_append_right (by try simp)]
    try simp
    unfold oneBitSetVec
    by_cases eq' : i = m
    · simp
      rw [List.getElem_set]
      rw [List.getElem_set]
      try simp
      subst eq'
      try simp
      have : i + 1 - j - 1 = i - j := by omega
      rw [this]
      unfold oneBitSet
      rw [Nat.add_mod]
      rw [Nat.pow_mod]
      simp
      by_cases eq : j < i
      · rw [Nat.zero_pow]; omega
      · simp at eq
        have : i < j := by simp at h; omega
        clear eq
        omega
    · simp
      rw [List.getElem_set]
      rw [List.getElem_set]
      simp

      -- rw [Vector.get_set_eq_if,
      --     Vector.get_replicate]
      -- try simp [eq']
      -- rw [Vector.get_set_eq_if]
      -- try simp
      by_cases eq'' : j = m
      · subst eq''
        try simp
        rw [Nat.succ_sub (Nat.le_of_lt_succ hi)]
        try simp
        -- rw [Nat.succ_sub (by try simp)]
        try simp
        rw [Nat.add_mod]
        rw [@oneBitSet_mod_2 (j - i) (Nat.lt_sub_of_add_lt (by try simp [Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq']))]
        try simp [oneBitSet]
      · try simp [eq'']
        try simp
        rw [Nat.succ_sub (Nat.le_of_lt_succ hi)]
        try simp
        rw [Nat.succ_sub (Nat.le_of_lt_succ hj)]
        try simp
        rw [Nat.add_mod]
        rw [@oneBitSet_mod_2 (m - i) (Nat.lt_sub_of_add_lt (by try simp [Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq']))]
        rw [@oneBitSet_mod_2 (m - j) (Nat.lt_sub_of_add_lt (by try simp [Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) eq'']))]
        try simp
        have : false :: List.replicate m false = List.replicate m.succ false := rfl
        simp [this]
        assumption
  · rw [List.getElem?_append (by try simp [Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hm) eq])] 
    unfold oneBitSetVec
    simp
    rw [List.getElem_set]
    rw [List.getElem_set]
    simp
    
    -- rw [Vector.get_set_eq_if, Vector.get_set_eq_if]
    -- try simp
    by_cases eq' : i = m
    · subst eq'
      try simp
      try simp
      rw [Nat.succ_sub (Nat.le_of_lt_succ hj)]
      try simp
      rw [Nat.succ_sub  (Nat.le_of_lt_succ hm)]
      try simp 
      by_cases eq'' : j = n
      · subst eq''
        try simp
        rw [Nat.add_div (by linarith)]
        have h_oneBit : oneBitSet (0 : ℕ) / (2 : ℕ) = 0 := by try simp [oneBitSet]
        simp [h_oneBit]
        try simp
        rw [oneBitSet_mod_2 (Nat.lt_sub_of_add_lt (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (by try simp [hm])) (by try simp[eq])))]
        try simp
        generalize eq_i_j : j - i = s
        rcases s with _ | s
        · aesop'
          have hh := Nat.le_antisymm (Nat.le_of_lt_succ hi) (by omega)
          aesop
        · rw [oneBitSet_div_2]
          rw [@Bitvec.ofNat_oneBitSet_eq_oneBitSetVec j ⟨s, by {
            apply Nat.lt_of_succ_le
            simp
            rw [←eq_i_j]
            exact Nat.sub_le _ _
          }⟩]
          try simp
          unfold oneBitSetVec
          try simp
          rw [List.getElem?_set, List.getElem?_replicate,
          ←Nat.sub_add_eq,
              Nat.add_one,
              Nat.succ_eq_add_one,
              ←eq_i_j,
              Nat.sub_sub_self (Nat.le_of_lt_succ hi)]
          try simp
          omega
      · specialize (@ih ⟨i, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq⟩ ⟨j, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) eq''⟩ (by {
          try simp at h
          try simp [h]
        }))
        have ih := congrArg (Function.swap Vector.get ⟨i, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq⟩) ih
        try try simp only [Function.swap] at ih
        unfold Bitvec.or at ih
        simp at ih
        rw [Vector.get_eq_get] at ih
        rw [Vector.get_eq_get] at ih
        rw [Vector.get_eq_get] at ih
        simp at ih
        rw [Bitvec.getElem_h_eq_getElem (by omega)] at ih
        rw [Bitvec.getElem_h_eq_getElem (by omega)] at ih
        rw [Bitvec.getElem_h_eq_getElem (by omega)] at ih
        generalize eq_n_j : n - j = s
        rcases s with _ | s
        · simp
          have hh := Nat.le_antisymm (Nat.le_of_lt_succ hj) (by omega)
          tauto
        · rw [eq_n_j] at ih
          try simp at ih
          rw [Nat.add_div (by linarith)]
          rw [oneBitSet_div_2]
          rw [oneBitSet_mod_2 (Nat.lt_sub_of_add_lt (by try simp [Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq]))]
          try simp
          rw [oneBitSet_mod_2 (by try simp)]
          try simp
          generalize eq_n_i : n - i = q
          rcases q with _ | q
          · simp
            have hh := Nat.le_antisymm (Nat.le_of_lt_succ hi) (by omega)
            tauto
          · rw [oneBitSet_div_2]
            rw [eq_n_i] at ih
            try simp at ih
            rw [List.getElem?_eq_getElem (by simp; omega)]
            rw [←ih]
            try simp
            left
            rw [←Option.some_inj]
            simp
            unfold oneBitSetVec
            simp [Vector.replicate]
    have : i ≠ j := by aesop
    clear h
    apply Bitvec.two_bits_set_aux₁ (ih := ih) (n := n) (m := m) (hm := hm) (hi := hi) (hj := hj) (eq := eq) (h := this) (eq' := eq')

theorem Bitvec.two_bits_set' {n : ℕ} {i j : Fin n} (h : i ≠ j) :
  Bitvec.or (oneBitSetVec n ⟨n - i - 1, by {
    try simp
    apply Nat.lt_of_lt_of_le
    apply Nat.sub_lt
    apply Nat.lt_sub_of_add_lt
    try simp
    linarith
    apply Nat.sub_le
  }⟩) (oneBitSetVec n ⟨n - j - 1, by {
    try simp
    apply Nat.lt_of_lt_of_le
    apply Nat.sub_lt
    apply Nat.lt_sub_of_add_lt
    try simp
    linarith
    apply Nat.sub_le
  }⟩) = Bitvec.ofNat n (oneBitSet i + oneBitSet j) := by
  rw [Bitvec.two_bits_set (by {
    try simp
    intro contr
    rw [←Nat.sub_add_eq,
        ←Nat.sub_add_eq,
        Nat.add_one,
        Nat.add_one,
        Nat.sub_succ,
        Nat.sub_succ] at contr
    have contr := Nat.pred_inj (by {
      apply Nat.lt_sub_of_add_lt
      try simp
    }) (by {
      apply Nat.lt_sub_of_add_lt
      try simp
    }) contr
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩ 
    try simp at contr
    zify [Nat.le_of_lt hi, Nat.le_of_lt hj] at contr
    have h' : ((↑n - ↑i):ℤ) = -(↑i - ↑n) := by ring_nf
    have h'' : ((↑n - ↑j):ℤ) = -(↑j - ↑n) := by ring_nf
    rw [h', h''] at contr
    rw [neg_inj] at contr
    rw [sub_left_inj] at contr
    try simp at h
    try simp at contr
    tauto
  })]
  try simp
  rcases i with ⟨i, hi⟩ 
  rcases j with ⟨j, hj⟩
  try simp 
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
    try simp
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
    try simp
    rw [Nat.sub_sub_self (Nat.le_of_lt_succ hj)]
  try simp [h', h'']

theorem Bitvec.or_and_distr_left {n : ℕ} {x y z : Bitvec n}:
  Bitvec.and x (Bitvec.or y z) = Bitvec.or (Bitvec.and x y) (Bitvec.and x z) := by
  unfold Bitvec.and Bitvec.or
  apply Vector.ext
  intro m
  simp [Bool.and_or_distrib_left]

@[simp]
theorem Bitvec.or_replicate_zero {n : ℕ} {x : Bitvec n} :
  Bitvec.or (Vector.replicate n false) x = x := by 
  apply Vector.ext
  intro m
  unfold Bitvec.or
  simp

theorem Bitvec.or_comm {n : ℕ} {x y : Bitvec n} :
  Bitvec.or x y = Bitvec.or y x := by
  apply Vector.ext
  intro m
  unfold Bitvec.or
  simp
  rw [Bool.or_comm]

theorem Bitvec.twoBitSet_and {n : ℕ} {i j : Fin n} {x : Bitvec n} : 
  (Bitvec.and x (Bitvec.or (oneBitSetVec n i) (oneBitSetVec n j))) = Vector.replicate n false 
    ∨ (Bitvec.and x (Bitvec.or (oneBitSetVec n i) (oneBitSetVec n j))) = oneBitSetVec n i
    ∨ (Bitvec.and x (Bitvec.or (oneBitSetVec n i) (oneBitSetVec n j))) = oneBitSetVec n j
    ∨ (Bitvec.and x (Bitvec.or (oneBitSetVec n i) (oneBitSetVec n j))) = (Bitvec.or (oneBitSetVec n i) (oneBitSetVec n j))  := by
  rw [Bitvec.or_and_distr_left]
  rcases (@oneSetBit_and _ i x) with h | h; rw [h]
  · rcases (@oneSetBit_and _ j x) with h' | h'; rw [h']
    · aesop
    · simp; tauto
  · rcases (@oneSetBit_and _ j x) with h' | h'; rw [h']
    · rw [Bitvec.or_comm]
      aesop
    · aesop

lemma sum_of_two_oneBitSet {i j : ℕ} (h : i ≠ j):
  oneBitSet i + oneBitSet j < oneBitSet (max i j + 1) := by
  unfold oneBitSet
  by_cases lt : i < j
  · apply Nat.le_trans
    apply Nat.add_lt_add_right
    apply pow_lt_pow_right
    linarith
    linarith
    rw [Nat.max_eq_right (by linarith)]
    ring_nf
    try simp
  · have lt := Nat.lt_of_le_of_ne (Nat.le_of_not_lt lt) (Ne.symm h)
    apply Nat.le_trans
    apply Nat.add_lt_add_left
    apply pow_lt_pow_right
    linarith
    exact lt
    rw [Nat.max_eq_left (by linarith)]
    ring_nf
    try simp


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
        · rcases i with ⟨-, ⟨⟩⟩
        · rw [Nat.succ_sub_one] at contr
          rcases i with ⟨i, hi⟩
          rcases j with ⟨j, hj⟩ 
          try simp
          try simp at contr
          zify [Nat.le_of_lt_succ hi, Nat.le_of_lt_succ hj] at contr
          have h' : ((↑n - ↑i):ℤ) = -(↑i - ↑n) := by ring_nf
          have h'' : ((↑n - ↑j):ℤ) = -(↑j - ↑n) := by ring_nf
          rw [h', h''] at contr
          rw [neg_inj] at contr
          rw [sub_left_inj] at contr
          try simp at contr
          exact contr
      · apply Nat.pow_le_pow_of_le_right (by linarith)
        apply Nat.add_le_of_le_sub
        omega
        omega
  })]
  rw [h',
      ←Bitvec.toNat_ofNat,
      ←Bitvec.two_bits_set h]

lemma Bitvec.ofNat_succ_allOnes_1 {n : ℕ} (h : 1 ≤ n):
  (Bitvec.ofNat (Nat.succ n) (allOnes 1)) = false ::ᵥ (Bitvec.ofNat n (allOnes 1)) := by
  apply Vector.ext
  rintro ⟨m, hm⟩ 
  rw [Vector.get_eq_get]
  rw [Vector.get_eq_get]
  simp only [Nat.succ_eq_add_one, Fin.cast_mk, List.get_eq_getElem, toList_cons]
  rw [Bitvec.getElem_h_eq_getElem (by omega)]
  simp [-all_ones_succ]
  rw [Bitvec.getElem_h_eq_getElem (by omega)]
  rw [Bitvec.allOnes_get]
  rcases m with _ | m
  · try simp
    generalize eq : Nat.ble n (0 : ℕ) = s
    cases s; try try simp
    rw [Nat.ble_eq] at eq
    aesop
  · simp only [add_tsub_cancel_right]
    rw [List.getElem_cons_succ]
    rw [Bitvec.getElem_h_eq_getElem (by omega)]
    rw [Bitvec.allOnes_get]
    try simp
    generalize eq : Nat.ble n (Nat.succ m) = s
    generalize eq' : Nat.ble (n - (1 : ℕ)) m = s'
    cases s
    · cases s'; try try simp
      rw [Nat.ble_eq] at eq'
      rw [ble_eq_false] at eq
      omega
    · cases s'
      · rw [Nat.ble_eq] at eq
        symm
        rw [←eq', Nat.ble_eq]
        aesop
      · rfl

@[simp]
theorem Bitvec.toNat_false_cons {n : ℕ} {x : Bitvec n} :
  Bitvec.toNat (false ::ᵥ x) = x.toNat := by
  match x with
  | ⟨.nil, _⟩ => aesop
  | ⟨.cons b x, _⟩ => 
    unfold Bitvec.toNat Bitvec.bitsToNat Bitvec.addLsb
    try simp

@[simp]
theorem Vector.replicate_zero {a : α} :
  Vector.replicate 0 a = Vector.nil := rfl

theorem Bitvec.ofNat_true_cons {n x: ℕ} (h : x < 2^n):
  true ::ᵥ Bitvec.ofNat n x = Bitvec.ofNat n.succ (2^n + x) := by
  induction' n with n ih generalizing x 
  · unfold Bitvec.ofNat Bitvec.ofNat
    try simp at h
    rw [h]
    try simp
    simp [Vector.append]
    rfl
  · rw [Bitvec.ofNat_succ]
    rw [Bitvec.ofNat_succ]
    rw [Nat.add_div (by linarith)]
    have h' : (2 : ℕ) ^ Nat.succ n / (2 : ℕ)  = 2^n := by
      have h : (2 : ℕ) ^ Nat.succ n / (2 : ℕ) = (2 : ℕ) ^ Nat.succ n / 2^1 := rfl
      rw [h, Nat.pow_div (by linarith) (by linarith)]
      try simp
    rw [h']
    have h' : (2 : ℕ) ^ Nat.succ n % (2 : ℕ) + x % (2 : ℕ) = x % 2 := by try simp [Nat.pow_succ, Nat.mul_mod]
    rw [h']
    have h' : ¬ (2 : ℕ) ≤ x % (2 : ℕ) := by
      intro contr
      have h := @Nat.mod_lt x 2 (by linarith)
      linarith
    try simp [h']
    rw [←ih (by {
      rw [Nat.div_lt_iff_lt_mul (by linarith),
          ←Nat.pow_succ]
      exact h
    })]
    have h' : ((2 : ℕ) ^ Nat.succ n + x) % (2 : ℕ) = x % 2 := by try simp [Nat.add_mod, Nat.pow_succ]
    rw [h']
    apply Vector.ext
    rintro ⟨m, hm⟩
    rw [Vector.get_eq_get, Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get, ←List.get?_eq_get]
    try simp


@[ simp]
theorem Bitvec.toNat_true_cons {n : ℕ} {x : Bitvec n} :
  Bitvec.toNat (true ::ᵥ x) = 2^n + x.toNat := by
  have h : 2^n + x.toNat = (2^n + x.toNat) % 2 ^ n.succ := by
    rw [Nat.mod_eq_of_lt]
    rw [Nat.add_comm]
    apply Nat.add_lt_of_lt_sub 
    have h : (2 : ℕ) ^ Nat.succ n - (2 : ℕ) ^ n = 2 ^ n := by
      rw [Nat.pow_succ]
      have h : (2 : ℕ) ^ n * (2 : ℕ) - (2 : ℕ) ^ n = (2 : ℕ) ^ n * (2 : ℕ) - ((2 : ℕ) ^ n) * 1 := by try simp
      rw [h, ←Nat.mul_sub_left_distrib] 
      try simp 
    rw [h]
    exact Bitvec.toNat_lt x
  rw [h, ←Bitvec.toNat_ofNat, ←Bitvec.ofNat_true_cons (Bitvec.toNat_lt x), Bitvec.ofNat_toNat]

@[ simp]
theorem Bitvec.ofNat_nil {x : ℕ}:
  Bitvec.ofNat 0 x = Vector.nil := by try simp [Bitvec.ofNat]

lemma Bitvec.lastBit' {x : Bitvec 1} :
  Bitvec.toNat (Bitvec.and x (Bitvec.ofNat 1 (allOnes 1))) = x.toNat % 2 := by
  rcases x with ⟨x, h⟩
  rcases x with _ | ⟨b, x⟩; try tauto
  rcases x with _ | ⟨b, x⟩
  · rw [Bitvec.ofNat_succ]
    try simp [Bitvec.ofNat_nil]
    unfold Bitvec.and Vector.map₂ Vector.append Bitvec.toNat bitsToNat addLsb
    try simp
    cases b; try aesop
    aesop
  · rw [Bitvec.ofNat_succ]
    try simp [Bitvec.ofNat_nil]
    unfold Bitvec.and Vector.map₂ Vector.append Bitvec.toNat bitsToNat addLsb
    try simp
    cases b; try aesop
    unfold cond
    simp at h
    simp at h

lemma Bitvec.lastBit'' {n : ℕ} {x : Bitvec n} (h : 1 < n):
  Bitvec.toNat (Bitvec.and x (Bitvec.ofNat n (allOnes 1))) = x.toNat % 2 := by
  induction x using Vector.inductionOn with
  | nil => cases h
  | @cons n b x ih =>
    have h := Nat.le_of_lt_succ h
    by_cases eq : n = 1
    · subst eq
      rw [Bitvec.ofNat_succ]
      have h' : allOnes (1 : ℕ) / (2 : ℕ) = 0 := by rfl
      rw [h']
      have h' : allOnes (1 : ℕ) % (2 : ℕ) = 1 := by rfl
      rw [h']
      try simp
      rw [Bitvec.ofNat_zero_eq_replicate]
      simp
      have : (false ::ᵥ nil).append (true ::ᵥ nil) = ⟨[false, true], rfl⟩ := rfl
      rw [this]
      have eq : x.toList = [true] ∨ x.toList = [false] := by aesop
      rcases eq with h' | h'
      · have p₁ : x = ⟨[true], rfl⟩ := by
          ext idx
          rw [Vector.get_eq_get]
          simp
          rcases idx with ⟨idx, hIdx⟩
          rw [Vector.get_eq_get]
          simp
          aesop
        have {h} : (Bitvec.and (b ::ᵥ x) ⟨[false, true], h⟩).toNat = 1 := by
          simp [Bitvec.and, map₂]
          split
          aesop'
          simp [Bitvec.toNat, bitsToNat, addLsb]
          injection heq
          aesop'
        simp [this]
        rcases b with _ | _
        · simp [p₁]; rfl
        · simp [p₁]; rfl
      · have p₁ : x = ⟨[false], rfl⟩ := by
          ext idx
          rw [Vector.get_eq_get]
          simp
          rcases idx with ⟨idx, hIdx⟩
          rw [Vector.get_eq_get]
          simp
          aesop
        have {h} : (Bitvec.and (b ::ᵥ x) ⟨[false, true], h⟩).toNat = 0 := by
          simp [Bitvec.and, map₂]
          split
          aesop'
          simp [Bitvec.toNat, bitsToNat, addLsb]
          injection heq
          aesop'
        simp [this]
        rcases b with _ | _
        · simp [p₁]; rfl
        · simp [p₁]; rfl
    · have h := Nat.lt_of_le_of_ne h (Ne.symm eq)
      rw [Bitvec.ofNat_succ_allOnes_1 (Nat.le_of_lt h)]
      unfold Bitvec.and
      try try simp only [Vector.map₂_cons, Bool.and_false, toNat_false_cons]
      unfold Bitvec.and at ih
      rw [ih h]
      cases b; try try simp
      try simp [Nat.add_mod]
      have h' : (2 : ℕ) ^ n % (2 : ℕ) % (2 : ℕ) = 0 := by
        rcases n with _ | n; try aesop
        try simp [Nat.pow_succ]
      rw [h']
      try simp

theorem Bitvec.lastBit {n : ℕ} {x : Bitvec n} (h : 1 ≤ n): 
  Bitvec.toNat (Bitvec.and x (Bitvec.ofNat n (allOnes 1))) = x.toNat % 2 := by
  by_cases eq : 1 = n
  · subst eq
    rw [Bitvec.lastBit']
  · have h := Nat.lt_of_le_of_ne h eq
    rw [Bitvec.lastBit'' h]

@[simp]
theorem Bitvec.toNat_nil :
  Bitvec.toNat Vector.nil = 0 := rfl

@[simp]
theorem Bitvec.ushr_nil {m : ℕ} :
  Bitvec.ushr Vector.nil m = Vector.nil := by
  rw [Vector.nil]
  simp [ushr, shiftRightFill, Vector.congr]
  aesop'
  congr
  cases l <;> aesop'
  simp at h

@[simp]
theorem Bitvec.ushr_cons_false {m n: ℕ} {x : Bitvec n}:
  Bitvec.ushr (false ::ᵥ x) m = false ::ᵥ Bitvec.ushr x m := by
  apply Vector.ext
  rintro ⟨i, hi⟩
  rw [Vector.get_eq_get]
  rw [Vector.get_eq_get]
  dsimp
  rw [Bitvec.getElem_h_eq_getElem (by omega)]
  rw [Bitvec.getElem_h_eq_getElem (by omega)]
  by_cases lt : i < m
  · rw [Bitvec.ushr_alternative₁' _ (by try simp [lt])]
    rcases i with _ | i; try try simp
    simp
    rw [Bitvec.getElem_h_eq_getElem (by omega)]
    rw [Bitvec.ushr_alternative₁']
    linarith
  · have lt := Nat.le_of_not_lt lt
    rw [Bitvec.ushr_alternative₂' _ (by try simp [lt])]
    try simp
    rcases i with _ | i; try try simp
    try simp
    symm
    by_cases eq : m = i.succ
    · subst eq
      try simp
      rw [Bitvec.getElem_h_eq_getElem (by omega)]
      rw [Bitvec.ushr_alternative₁' _ (by try simp)]
    · have lt := Nat.lt_of_le_of_ne lt eq
      rw [Bitvec.getElem_h_eq_getElem (by omega)]
      rw [Bitvec.ushr_alternative₂' _ (by omega)]
      have : i + 1 - m = (i - m) + 1 := by omega
      simp [this]
      
@[simp]
theorem Bitvec.toNat_cong {a b : ℕ} {x : Bitvec a} {h : a = b}:
  Bitvec.toNat (Bitvec.cong h x) = Bitvec.toNat x := by
  unfold Bitvec.cong Bitvec.toNat
  rcases x with ⟨x, _⟩ 
  simp [Vector.congr]

@[ simp]
theorem Bitvec.toNat_append_full {n m: ℕ} {x : Bitvec n} {y : Bitvec m} :
  Bitvec.toNat (Vector.append x y) = 2^m * (Bitvec.toNat x) + Bitvec.toNat y := by
  induction x using Vector.inductionOn generalizing m y with
  | nil => 
    try simp
    have h : Vector.append Vector.nil y = Bitvec.cong (by try simp) y := by
      apply Vector.ext
      rintro ⟨i, hi⟩
      rw [@Bitvec.get_cong _ _ _ ⟨i, by {
        try simp at hi
        tauto
      }⟩ _ (by try simp) (by try simp)]
      rw [Vector.get_eq_get, Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get, ←List.get?_eq_get]
      try simp
    try simp [h]
  | @cons n b x ih =>
    have h : Vector.append (b ::ᵥ x) y = Bitvec.cong (by linarith) (b ::ᵥ Vector.append x y) := by
      apply Vector.ext
      rintro ⟨i, hi⟩
      rw [@Bitvec.get_cong _ _ _ ⟨i, by {
        try simp at hi
        linarith
      }⟩ _ (by linarith) (by try simp)]
      rw [Vector.get_eq_get, Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get, ←List.get?_eq_get]
      try simp
    try simp [h]
    cases b
    · try simp
      rw [ih]
    · try simp
      rw [ih]
      ring_nf
      try simp
  
theorem Bitvec.ushr_eq {n m : ℕ} {x : Bitvec n} (h : m ≤ n) :
  x.ushr m = Bitvec.cong (by try simp [Nat.add_sub_cancel', h]) (Vector.append (Vector.replicate m false) (Vector.take (n - m) x)) := by
  apply Vector.ext
  rintro ⟨i, hi⟩
  by_cases lt : i < m
  · rw [@Bitvec.get_cong _ _ _ ⟨i, by {
          try simp at hi
          try simp [Nat.add_sub_cancel', h, hi]
        }⟩ _ (by {
          try simp [Nat.add_sub_cancel', h]
        }) (by try simp)]
    rw [Vector.get_eq_get]
    rw [Vector.get_eq_get]
    dsimp
    rw [Bitvec.getElem_h_eq_getElem (by omega)]
    rw [Bitvec.getElem_h_eq_getElem (by omega)]
    rw [Bitvec.ushr_alternative₁' _ (by try simp [lt])]
    simp
    rw [List.getElem_append_left _ _ (by aesop)]
    simp
  · have lt := Nat.le_of_not_lt lt
    rw [@Bitvec.get_cong _ _ _ ⟨i, by {
          try simp at hi
          try simp [Nat.add_sub_cancel', h, hi]
        }⟩ _ (by {
          try simp [Nat.add_sub_cancel', h]
        }) (by try simp)]
    rw [Vector.get_eq_get]
    rw [Vector.get_eq_get]
    dsimp
    rw [Bitvec.getElem_h_eq_getElem (by omega)]
    rw [Bitvec.getElem_h_eq_getElem (by omega)]
    rw [Bitvec.ushr_alternative₂' _ (by try simp [lt])]
    simp
    rw [List.getElem_append_right _ _ (by aesop)]
    simp
    rw [Bitvec.getElem_h_eq_getElem (by omega)]
    rw [←List.getElem_take]
    rfl
    omega
    simp
    omega

-- theorem Nat.pow_add (a m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
--   induction n with
--   | zero => rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
--   | succ _ ih => rw [Nat.add_succ, Nat.pow_succ, Nat.pow_succ, ih, Nat.mul_assoc]

theorem Bitvec.toNat_take {n m : ℕ} {x : Bitvec n} (h : m < n) : 
  Bitvec.toNat x / (2 : ℕ) ^ m = Bitvec.toNat (Vector.take (n - m) x) := by
  induction x using Vector.inductionOn generalizing m with
  | nil => 
    try simp at h
  | @cons n b x ih =>
    have h' : Vector.take (Nat.succ n - m) (b ::ᵥ x) = Bitvec.cong (by {
      try simp
      rw [Nat.succ_sub (by linarith)]
    }) (b ::ᵥ Vector.take (n - m) x) := by
      apply Vector.ext
      rintro ⟨i, hi⟩
      rw [@Bitvec.get_cong _ _ _ ⟨i, by {
          try simp at hi
          try simp
          rw [Nat.succ_sub (by linarith)] at hi
          exact hi
        }⟩ _ (by {
          try simp
          rw [Nat.succ_sub (by linarith)]
        }) (by try simp),
        Vector.get_eq_get,
        Vector.get_eq_get,
        ←Option.some_inj,
        ←List.get?_eq_get,
        ←List.get?_eq_get]
      try simp
      rw [Nat.succ_sub (by linarith)]
      try simp
    rw [h']
    try simp
    have h' := Nat.le_of_lt_succ h
    by_cases eq : m = n
    · subst eq
      try simp
      have h'' : Vector.take (m - m) x = Bitvec.cong (by try simp) Vector.nil := by
        apply Vector.ext
        rintro ⟨i, hi⟩
        try simp at hi
      cases b
      · try simp
        simp [h'']
        rw [Nat.div_eq_zero_iff]
        apply Bitvec.toNat_lt
        cases m <;> simp
      · try simp
        simp [h'']
        rw [Nat.div_eq_zero_iff]
        apply Bitvec.toNat_lt
        cases m <;> simp
    · have lt := Nat.lt_of_le_of_ne h' eq
      cases b
      · try simp
        rw [ih lt]
      · try simp
        rw [Nat.add_div (by aesop), ih lt]
        have h_mod : (2 : ℕ) ^ n % (2 : ℕ) ^ m = 0 := by
          have h : n = (n - m + m) := by 
            zify [Nat.le_of_lt lt]
            try simp
          rw [h]
          have h : (2 : ℕ) ^ (n - m + m) = (2 : ℕ) ^ (n - m) * (2 : ℕ) ^ m := by
            rw [←Nat.pow_add 2 (n - m) m]  
          rw [h, Nat.mul_mod]
          try simp
        rw [h_mod]
        try simp
        have h_not : ¬ (2 : ℕ) ^ m ≤ Bitvec.toNat x % (2 : ℕ) ^ m := by
          intro contr
          have contr := Nat.lt_of_le_of_lt contr (Nat.mod_lt _ (by aesop))
          linarith
        try simp [h_not]
        rw [Nat.pow_div (Nat.le_of_lt lt) (by linarith)]
      


theorem Bitvec.ushr_toNat {n m : ℕ} {x : Bitvec n} :
  x.toNat / (2 ^ m) = (x.ushr m).toNat := by
  by_cases le : m ≤ n
  · rw [Bitvec.ushr_eq le]
    try simp
    by_cases eq: m = n
    · subst eq
      have h'' : Vector.take (m - m) x = Bitvec.cong (by try simp) Vector.nil := by
        apply Vector.ext
        rintro ⟨i, hi⟩
        try simp at hi
      rw [h'']
      try simp
      rw [Nat.div_eq_zero_iff]
      apply Bitvec.toNat_lt
      cases m <;> simp
    · have lt := Nat.lt_of_le_of_ne le eq
      rw [Bitvec.toNat_take lt]
  · have lt := Nat.lt_of_not_le le
    rw [Bitvec.ushr_full_length (Nat.le_of_lt lt)]
    try simp
    rw [Nat.div_eq_zero_iff]
    transitivity 2^n
    apply Bitvec.toNat_lt
    rw [Nat.pow_lt_pow_iff_right]
    omega; decide; cases m; cases lt; aesop

theorem Bitvec.ushr_ofNat {n m x: ℕ} (h: x < 2 ^ n) :
  ((Bitvec.ofNat n x).ushr m) = Bitvec.ofNat n (x / 2 ^ m) := by
  have h' : x = x % (2 ^ n) := by rw [Nat.mod_eq_of_lt h]
  symm
  rw [h', ←Bitvec.toNat_ofNat,
      Bitvec.ushr_toNat,
      Bitvec.ofNat_toNat,
      Bitvec.ofNat_toNat]

theorem Bitvec.allOnes_ushr {n m i : ℕ} (h : i ≤ n) (h' : m ≤ i):
  Bitvec.ushr (Bitvec.ofNat n (allOnes i)) m = Bitvec.ofNat n (allOnes (i - m)) := by
  rw [Bitvec.ushr_ofNat (by {
    try simp [allOnes]
    exact Nat.lt_of_lt_of_le (Nat.sub_lt (by try simp) (by linarith)) (Nat.pow_le_pow_of_le_right (by linarith) h)
  })]
  unfold allOnes
  have h'' : (2 : ℕ) ^ i = 2^m * 2^(i-m) := by rw [←Nat.pow_add,
                                                   Nat.add_sub_of_le h']
  rw [h'']
  have h'' : (((2 : ℕ) ^ m * (2 : ℕ) ^ (i - m) - (1 : ℕ)) / (2 : ℕ) ^ m)  = ((2 : ℕ) ^ (i - m) - (1 : ℕ)) := by
    rw [Nat.mul_sub_div 0 (2^m) (2^(i-m)) (by try simp)]  
    try simp
  rw [h'']

@[ simp]
theorem Bitvec.toList_cong {a b : ℕ} {x : Bitvec a} {h : a = b}:
  Vector.toList (Bitvec.cong h x) = Vector.toList x := by
  rcases x with ⟨x, _⟩
  simp [Vector.congr, Bitvec.cong]

theorem Bitvec.get_toNat_div {n x : ℕ} {i : Fin n} (h : ↑i.succ < n):
  (Bitvec.ofNat n (x / 2))[↑i.succ]'h = (Bitvec.ofNat n x)[i] := by
  induction' n with n ih generalizing x
  · try simp at h
  · rw [←Option.some_inj]
    rw [Bitvec.ofNat_succ, Bitvec.ofNat_succ]
    try simp
    rcases i with ⟨i, hi⟩ 
    by_cases eq : i + 1 = n
    · subst eq
      simp
      rw [List.getElem_append]
      rw [Bitvec.getElem_h_eq_getElem]
      rw [Bitvec.ofNat_succ]
      try simp
      omega
      
    · try simp at h
      have h := Nat.lt_of_le_of_ne h eq
      try simp
      rw [List.getElem_append]; swap; simp; omega
      specialize (@ih (x / 2) ⟨i, by linarith⟩ (by try simp [h]))
      try simp at ih
      rw [ih, List.getElem_append]


theorem Bitvec.get_ofNat_succ {n x : ℕ} {i : Fin n} :
  (Bitvec.ofNat n x)[i] = (Bitvec.ofNat n.succ x)[Fin.succ i] := by
  try simp
  rcases i with ⟨i, hi⟩ 
  try simp
  rw [Bitvec.getElem_h_eq_getElem hi]
  rw [Bitvec.getElem_h_eq_getElem (by linarith)]
  induction x using Nat.case_strong_induction_on generalizing i n with
  | hz =>
    generalize eq : (Bitvec.ofNat (n + 1) 0)[i + 1] = s
    rw [←@Bitvec.toNat_replicate_false_eq_zero n, Bitvec.ofNat_toNat, ←eq]
    have : Bitvec.toNat (replicate (n + 1) false) = 0 := Bitvec.toNat_replicate_false_eq_zero
    have : Bitvec.ofNat (n + 1) 0 = Bitvec.ofNat (n + 1) (Bitvec.toNat (replicate (n + 1) false)) := by aesop
    simp only [this]
    simp only [Bitvec.ofNat_toNat]
    rfl
  | hi x ih =>
    rw [Bitvec.ofNat_succ] 
    try simp
    by_cases eq : i.succ = n
    · simp only [←Nat.succ_eq_add_one]
      rw [List.getElem_append_right]; swap; simp; omega
      simp
      rcases n with _ | n <;> [tauto;skip]
      rw [Bitvec.ofNat_succ]; simp
      rw [List.getElem_append_right]; swap; aesop
      simp
      have : i - (toList (Bitvec.ofNat n ((x + 1) / 2))).length = 0 := by simp; omega
      rw [this]
      simp
      simp; omega
    · rw [List.getElem_append]; swap; simp; omega
      rw [Bitvec.getElem_h_eq_getElem]
      rw [Bitvec.getElem_h_eq_getElem]
      rw [ih ((x + 1) / 2) (by {
        have h := @Nat.div_lt_self x.succ 2 (by linarith) (by linarith)
        exact Nat.le_of_lt_succ h
      }) _ (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hi) eq)]
      rw [Bitvec.ofNat_succ]
      simp
      by_cases eq' : i.succ.succ = n
      · subst eq'
        rw [List.getElem_append_right]; swap; simp
        try simp
        rw [Bitvec.ofNat_succ]
        try simp
        rw [List.getElem_append]; swap; simp
        try simp
        rw [Bitvec.ofNat_succ]
        simp
        simp
      · rw [List.getElem_append]; swap; simp; omega
        have h_get := @Bitvec.get_toNat_div n (Nat.succ x / 2) ⟨i + 1, (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hi) eq)⟩ (by {
          try simp
          exact Nat.lt_of_le_of_ne (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hi) eq)) eq'
        })
        simp only [Nat.succ_eq_add_one, Fin.succ_mk, Fin.getElem_fin] at h_get
        rw [Bitvec.getElem_h_eq_getElem]
        rw [h_get]
        have h_get := @Bitvec.get_toNat_div n (Nat.succ x) ⟨i, hi⟩ (by {
          try simp
          exact (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hi) eq)
        })
        simp only [Nat.succ_eq_add_one, Fin.succ_mk, Fin.getElem_fin] at h_get
        rw [h_get]

theorem Bitvec.drop_ofNat {m n x : ℕ} (h : m ≤ n):
  Bitvec.ofNat m x = Bitvec.cong (by rw [Nat.sub_sub_self h]) (Vector.drop (n - m) (Bitvec.ofNat n x)) := by
    induction' n with n ih generalizing m x
    · try simp at h
      subst h
      try simp [Bitvec.cong, Vector.congr, drop, nil]
    · by_cases eq : m = Nat.succ n
      · subst eq
        rw [Bitvec.ofNat_succ]
        apply Vector.ext
        rintro ⟨i, hi⟩
        rw [Vector.get_eq_get, Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get, ←List.get?_eq_get]
        try simp
      · rw [ih (by omega)]
        apply Vector.ext
        rintro ⟨i, hi⟩
        rw [Vector.get_eq_get, Vector.get_eq_get]
        try simp
        simp only [←Nat.succ_eq_add_one]
        rw [←List.getElem_drop, ←List.getElem_drop]; swap; simp; omega; swap; simp; omega
        simp only [Bitvec.ofNat_succ]
        try simp
        by_cases eq' : m = i.succ
        · subst eq'
          try simp
          have : n - (i + 1) + i = n - 1 := by omega
          simp only [this]
          rw [List.getElem_append_right]; swap; simp; omega; swap; simp; omega
          try simp
          rcases n with _ | n
          simp at this; subst this; simp at *;
          simp at eq
          simp only [←Nat.succ_eq_add_one]
          simp [Bitvec.ofNat_succ]
        · rw [List.getElem_append]; swap; simp; omega
          have h_get := @Bitvec.get_toNat_div n x ⟨n - m + i, by {
            apply Nat.lt_of_lt_of_le
            apply Nat.add_lt_add_left hi
            rw [Nat.sub_add_cancel (by omega)]
          }⟩ (by simp; omega)
          try simp at h_get
          rw [←h_get]
          congr 1
          omega

theorem Bitvec.drop_ofNat' {m n x : ℕ} (h : m ≤ n):
  (Vector.drop (n - m) (Bitvec.ofNat n x)) = Bitvec.cong (by rw [Nat.sub_sub_self h]) (Bitvec.ofNat m x) := by 
  apply Vector.ext
  rintro ⟨i, hi⟩
  rw [@Bitvec.get_cong _ _ _ ⟨i, by {
          rw [Nat.sub_sub_self h] at hi
          try simp [hi]
        }⟩ _ (by rw [Nat.sub_sub_self h]) (by try simp)]
  rw [Vector.get_eq_get, Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get, ←List.get?_eq_get]
  try simp
  have h' := @Bitvec.drop_ofNat m n x h
  have h' := congrArg (Function.swap Vector.get ⟨i, by {
    rw [Nat.sub_sub_self h] at hi
    exact hi
  }⟩) h' 
  try simp [Function.swap] at h'
  rw [Vector.get_eq_get, Vector.get_eq_get, ←Option.some_inj, ←List.get?_eq_get, ←List.get?_eq_get] at h'
  try simp at h'
  rw [←h']

theorem Bitvec.ofNat_and_allOnes {n m : ℕ} {x : Bitvec n} :
  Bitvec.and x (Bitvec.ofNat n (allOnes (m : ℕ))) = Bitvec.ofNat n (x.toNat % (2 ^ m)) := by
  by_cases le : m ≤ n
  · rw [←Bitvec.toNat_ofNat,
        @Bitvec.drop_ofNat m n _ le]
    try simp
    rw [Bitvec.ofNat_toNat]
    have h : Bitvec.toNat (Vector.drop (n - m) x) = Bitvec.toNat (Vector.append (Vector.replicate (n - m) false) (Vector.drop (n - m) x)) := by try simp
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
    rw [Bitvec.and_allOnes_eq_get, Vector.get_eq_get, Vector.get_eq_get]
    try simp
    by_cases lt : i < n - m
    · try simp [lt]
      rw [List.getElem_append, List.getElem_replicate]
      simp; exact lt
    · try simp [lt]
      rw [List.getElem_append_right]; swap; simp; omega
      simp
      rw [←List.getElem_drop]; swap; simp; omega
      have : n - m + (i - (n - m)) = i := by omega
      simp only [this]
      simp
      omega
  · try simp at le
    rw [Nat.mod_eq_of_lt (Nat.lt_trans (Bitvec.toNat_lt x) (pow_lt_pow_right (by linarith) le)),
        Bitvec.ofNat_toNat]
    apply Vector.ext
    intro i
    rw [Bitvec.and_allOnes_eq_get, Nat.sub_eq_zero_of_le (Nat.le_of_lt le)]
    try simp



theorem Bitvec.toNat_and_allOnes {n m : ℕ} {x : Bitvec n} :
  Bitvec.toNat (Bitvec.and x (Bitvec.ofNat n (allOnes (m : ℕ)))) = x.toNat % (2 ^ m) := by
  by_cases lt : m < n
  · rw [Bitvec.ofNat_and_allOnes,
        Bitvec.toNat_ofNat,
        Nat.mod_eq_of_lt (by {
          apply Nat.lt_trans
          apply Nat.mod_lt _ (by try simp)
          exact pow_lt_pow_right (by linarith) lt
        })]
  · try simp at lt
    rw [Bitvec.ofNat_and_allOnes,
        Bitvec.toNat_ofNat,
        Nat.mod_eq_of_lt (by {
          rw [Nat.mod_eq_of_lt]
          apply Nat.lt_of_lt_of_le
          apply Bitvec.toNat_lt
          try simp
          apply Nat.lt_of_lt_of_le
          apply Bitvec.toNat_lt
          apply Nat.pow_le_pow_of_le_right (by linarith) lt
        })]
    

theorem Bitvec.and_ofNat_allOnes {n m x : ℕ} (h : x < 2 ^ m) (h' : m ≤ n):
  Bitvec.ofNat n x = Bitvec.and (Bitvec.ofNat n x) (Bitvec.ofNat n (allOnes m)) := by
  rw [←Bitvec.ofNat_toNat (Bitvec.and (Bitvec.ofNat n x) (Bitvec.ofNat n (allOnes m))), 
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
