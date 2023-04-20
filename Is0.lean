import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs

@[inline]
def P: ℕ := 15 * 2^27 + 1

axiom P_prime: Nat.Prime P 
instance : Fact (Nat.Prime P) := ⟨P_prime⟩
abbrev Felt := ZMod P
def Constraint := Prop

inductive Literal where
  | Val : Felt → Literal
  | Constraint : Constraint → Literal

def State := Std.HashMap String Literal

-- We'll definitely need a context, mapping variable names to values.

inductive Cirgen where
  | Const : Felt → Cirgen
  | True : Cirgen
  | Get : Vector Felt n → Fin n → Felt → Cirgen
  | Set : Vector Felt n → Fin n → Felt → Cirgen
  | Sub : Felt → Felt → Cirgen
  | Mul : Felt → Felt → Cirgen
  | Isz : Felt → Cirgen
  | Inv : Felt → Cirgen
  | AndEqz : Constraint → Felt → Cirgen
  | AndCond : Constraint → Felt → Constraint → Cirgen
  | Variable : String → Cirgen
  | Sequence : Cirgen → Cirgen → Cirgen
  | Assign : String → Literal → Cirgen

def Cirgen.step (state : State) (op : Cirgen) : Literal :=
  match op with
  | Const x => .Val x
  | True => .Constraint (_root_.True)
  | Get buffer i _ => .Val (buffer.get i)
  | Sub x y => .Val (x - y)
  | Variable name => (state.findD name (Literal.Val 0))
  | AndEqz c x => .Constraint (c ∧ x = 0)
  | Sequence a b => .Constraint False
  | Assign name x => state.
  | _ => .Constraint False

open Cirgen in
theorem Sub_AndEqz_is_if_is_zero : ∀ x : Felt, Sequence (Sub x 1) (AndEqz True state.get "%0") := by sorry
