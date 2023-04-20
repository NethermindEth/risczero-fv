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

inductive Thing : Type → Type where
  | Literal {a} : a → Thing a
  | Variable {a} : String → Thing a

inductive Expression where
  | Const : Felt → Expression
  | True : Expression
  | Get : Vector Felt n → Fin n → Felt → Expression
  | Set : Vector Felt n → Fin n → Felt → Expression
  | Sub : Felt → Felt → Expression
  | Mul : Felt → Felt → Expression
  | Isz : Felt → Expression
  | Inv : Felt → Expression
  | AndEqz : ConstraintThing → FieldThing → Expression
  | AndCond : Constraint → Felt → Constraint → Expression
  | Variable : String → Expression

def Expression.eval (state : State) (e : Expression) : Literal :=
  match e with
  | Const x => .Val x
  | True => .Constraint (_root_.True)
  | Get buffer i _ => .Val (buffer.get i)
  | Sub x y => .Val (x - y)
  | Variable name => state.findD name (Literal.Val 0)
  | AndEqz c x => .Constraint (c ∧ x = 0)
  | _ => .Constraint False

def Expression.assign (state : State) (e : Expression) (name : String) : State :=
  state.insert name (Expression.eval state e)

inductive Cirgen where
  | Sequence : Cirgen → Cirgen → Cirgen
  | Assign : String → Expression → Cirgen
  -- Should this take a String?
  | Return : Expression → Cirgen

def Cirgen.step (state : State) (op : Cirgen) : State × Option Literal :=
  match op with
  -- We may want to encode the index of the instruction in `State`, and then
  -- always assign to the index instead of using a name.
  | Assign e name => (Expression.assign state e name, none)
  | Sequence a b => let (state', x) := Cirgen.step state a
                    match x with
                    | some x => (state', some x)
                    | none => Cirgen.step state' b
  | Return e => (state, Expression.eval state e)

open Expression Cirgen in
theorem Sub_AndEqz_is_if_is_zero (state : State) :
  ∀ x : Felt, Sequence (Assign "x-1" (Expression.Sub x 1)) (Assign "(x-1)=0" (AndEqz True (Variable "x-1"))) := by sorry
