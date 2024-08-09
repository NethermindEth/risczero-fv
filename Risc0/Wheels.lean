import Mathlib.Data.Vector.Basic

namespace Option

@[simp]
lemma get!_of_some {α : Type} [Inhabited α] (x : α) : (some x).get! = x := rfl

lemma not_isNone_iff_isSome {α : Type} [Inhabited α] {x : Option α} :
  ¬x.isNone ↔ x.isSome := by
  rw [Option.isNone_iff_eq_none, ←ne_eq, Option.ne_none_iff_isSome]

lemma not_isEqSome_of_isNone {α : Type} [Inhabited α] [BEq α] {x : Option α} {y : α} (h : x.isNone) :
  ¬x.isEqSome y := by unfold isNone isEqSome at *; aesop

end Option

namespace List

section

variable {α : Type} {l : List α}

def push (x : α) (l : List α) : List α :=
  l ++ [x]

lemma get!_set_of_lt_length [Inhabited α] (h : i < l.length) :
  List.get! (List.set l i x) i = x := by
  induction l generalizing i with
    | nil => cases h
    | cons hd tl ih => cases i <;> aesop

lemma get!_set_of_ne [Inhabited α] (h : i ≠ i') :
  List.get! (List.set l i v) i' = List.get! l i' := by
  induction l generalizing i' i with
    | nil => simp
    | cons hd tl ih =>
      unfold List.get! List.set
      aesop

end

end List

namespace Mathlib.Vector

def push {α : Type} {k : ℕ} (x : α) : Vector α k → Vector α (k + 1)
  | ⟨l, h⟩ => ⟨l.push x, by simp [List.push, h]⟩

end Mathlib.Vector

lemma if_congr_of_and [Decidable c] [Decidable c'] (h : c = c' ∧ t = t' ∧ f = f') :
  (if c then t else f) = if c' then t' else f' := by aesop

namespace Risc0

namespace Wheels

end Wheels

register_option pp.explicitOfNat : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display implicit arguments of ofNat"
}

open Lean Elab Tactic in
elab "aesop'" : tactic => do
  evalTactic <| ← `( tactic|
    aesop (config := { warnOnNonterminal := false })
  )

end Risc0
