import Mathlib.Data.Option.Basic

namespace Risc0

def Map (α : Type) (β : Type) := α → Option β

namespace Map

section Map

variable {α : Type} [DecidableEq α] {β : Type}

def empty : Map α β := λ _ => none

def update (m : Map α β) (k : α) (v : β) : Map α β :=
  λ x => if x = k then some v else m x

end Map

end Map

notation:61 m "[" k:61 "]" " ←ₘ " v:49 => Map.update m k v

section Map.Instances

variable {α β : Type} [DecidableEq α]

-- Todo: Membership in terms of GetElem
-- k ∈ m
instance : Membership α (Map α β) := ⟨λ k m => (m k).isSome⟩

-- m[k]
instance : GetElem (Map α β) α (Option β) (λ _ _ => True) := ⟨λ m k _ => m k⟩

-- macro_rules
-- | `(tactic| get_elem_tactic_trivial) => `(tactic| simp only)

end Map.Instances

namespace Map

section Map

variable {α : Type} [DecidableEq α] {β : Type}
         {m : Map α β} {k k' : α} {v v' : β}

-- def get (h : k ∈ m) := m[k].get h

-- def get! [Inhabited β] (m : Map α β) (k : α) := m[k].get!

lemma update_def : update m k v = λ x => if x = k then some v else m x := rfl

-- lemma get_def (h : k ∈ m) : m.get h = m[k].get h := rfl

def fromList (l : List (α × β)) : Map α β :=
  match l with
    | [] => Map.empty
    | (k, v) :: xs => (Map.fromList xs)[k] ←ₘ v

lemma getElem_def : m[k] = m k := rfl

-- @[simp]
-- lemma get!_def [Inhabited β] : get! (m[k] ←ₘ v) k = v := by
--   simp [get!, getElem_def, update, Option.get!]

@[simp]
lemma fromList_nil : fromList ([] : List (α × β)) = Map.empty := rfl

@[simp]
lemma fromList_cons {l : List (α × β)} :
  fromList ((k, v) :: l) = (Map.fromList l)[k] ←ₘ v := rfl

lemma update_neq_comm (h : k ≠ k') : ((m[k] ←ₘ v)[k'] ←ₘ v') = ((m[k'] ←ₘ v')[k] ←ₘ v) := by
  simp [update]
  funext x
  by_cases eq: x = k
  subst eq
  simp
  aesop
  simp only
  by_cases eq': x = k'
  subst eq'
  simp only [ite_true]
  aesop
  aesop

@[simp]
lemma update_get : (m[k] ←ₘ v)[k] = v := by simp [update, getElem_def]

@[simp]
lemma update_get! : (m[k] ←ₘ v)[k]! = v := by simp [update, getElem!, getElem_def]

@[simp]
lemma empty_get : (@Map.empty α β)[k] = none := by rfl

lemma update_get_skip (h : k ≠ k') (h₁ : m[k] = some v) :
  (m[k'] ←ₘ v')[k] = some v := by simp [update, h, getElem_def, getElem_def ▸ h₁]

lemma update_get_next (h : k ≠ k') :
  (m[k] ←ₘ v)[k'] = m[k'] := by simp [update, getElem_def, h.symm]

-- Membership lemmas.
lemma mem_def : (x ∈ m) = m[x].isSome := rfl

@[simp]
lemma mem_update_self : k ∈ m[k] ←ₘ v := by
  rw [mem_def, Option.isSome_iff_exists, update_get]; use v

lemma mem_skip (h : k ∈ m) : k ∈ m[k'] ←ₘ v := by simp [mem_def, getElem_def, update]; aesop

@[simp]
lemma not_mem_empty : k ∉ @empty α β :=
  λ contra => by simp [Map.mem_def, getElem_def, empty] at contra

@[simp]
lemma not_empty_eq_some : ¬Option.isSome (@empty α β var) = true := not_mem_empty

lemma mem_update_of_ne (h : k ≠ k') (h₁ : k ∈ m[k'] ←ₘ v) : k ∈ m := by
  rw [mem_def, getElem_def] at *; unfold update at h₁; aesop

lemma mem_fromList {l : List (α × β)} : k ∈ fromList l ↔ k ∈ l.map Prod.fst := by
  induction l with
    | nil => simp
    | cons hd tl ih =>
        rcases hd with ⟨k', v'⟩
        rw [List.map_cons, List.mem_cons, ←ih]; simp
        apply Iff.intro <;> intros h <;> {
          rw [mem_def, getElem_def] at h ⊢; unfold Map.update at *
          aesop
        }

lemma mem_unroll_assignment : k ∈ m[k'] ←ₘ v ↔ (k = k' ∨ k ∈ m) := by
  simp [update, mem_def, getElem_def]; aesop

lemma not_mem_iff_none : k ∉ m ↔ m[k] = none := by
  rw [mem_def]; rw [getElem_def] at *; aesop; rwa [Option.isNone_iff_eq_none] at a

end Map

end Map

instance {α β : Type} [DecidableEq α] {m : Map α β} {k : α} : Decidable (k ∈ m) :=
  Map.mem_def ▸ inferInstance

section tactics

open Lean Elab Tactic

-- Probably the simplest way to decide membership for maps that contain metavariables.
-- E.g. 42 ∈ empty[42] := k.succ.
elab "decide_mem_map" : tactic => do
  evalTactic <| ← `(
    tactic| repeat ( first | apply Map.mem_update_self | apply Map.mem_skip )
  )

end tactics

end Risc0
