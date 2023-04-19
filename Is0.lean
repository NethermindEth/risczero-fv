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

inductive Literal where
  | Val : Val → Literal
  | Constraint : Constraint → Literal

inductive Cirgen where
  | Const : Val → Cirgen
  | True : Cirgen
  | Get : Vector Val n → Fin n → Val → Cirgen
  | Set : Vector Val n → Fin n → Val → Cirgen
  | Sub : Val → Val → Cirgen
  | Mul : Val → Val → Cirgen
  | Isz : Val → Cirgen
  | Inv : Val → Cirgen
  | AndEqz : Constraint → Val → Cirgen
  | AndCond : Constraint → Val → Constraint → Cirgen
  | Variable : String → Cirgen

def Cirgen.step (state : State) (constraints : List Constraint) (op : Cirgen) : Literal :=
  match op with
  | Const x => Literal.Val x
  | True => Literal.Constraint (¬ False)
  | Get buffer i _ => Literal.Val (buffer.get i)
  | Sub x y => Literal.Val (x - y)
  | Variable name => Literal.Val (state.findD name 0)
