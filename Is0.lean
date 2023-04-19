import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs

@[inline]
def P: ℕ := 15 * 2^27 + 1

axiom P_prime: Nat.Prime P 
instance : Fact (Nat.Prime P) := ⟨P_prime⟩
abbrev Val := ZMod P
abbrev State := Std.HashMap String Val
abbrev Constraint := Prop

inductive Cirgen where
  | Const : Val → Cirgen
  | True : Cirgen
  | Get : Vector ℕ n → Fin n → Val → Cirgen
  | Set : Vector ℕ n → Fin n → Val → Cirgen
  | Sub : Val → Val → Cirgen
  | Mul : Val → Val → Cirgen
  | Isz : Val → Cirgen
  | Inv : Val → Cirgen
  | AndEqz : Constraint → Val → Cirgen
  | AndCond : Constraint → Val → Constraint → Cirgen
  | Variable : String → Cirgen
