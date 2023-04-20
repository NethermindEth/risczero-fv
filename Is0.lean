import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs

@[inline]
def P: ℕ := 15 * 2^27 + 1

axiom P_prime: Nat.Prime P 
instance : Fact (Nat.Prime P) := ⟨P_prime⟩
abbrev Felt := ZMod P
def Constraint := Prop

inductive Lit where
  | Val : Felt → Lit
  | Constraint : Constraint → Lit

def State := Std.HashMap String Lit

-- We'll definitely need a context, mapping variable names to values.

inductive Expression : Type → Type where
  | Literal {a} : a → Expression a
  | Variable {a} : String → Expression a

inductive Op where
  | Const : Felt → Op
  | True : Op
  | Get : Vector Felt n → Fin n → Felt → Op
  | Set : Vector Felt n → Fin n → Felt → Op
  | Sub : Felt → Felt → Op
  | Mul : Felt → Felt → Op
  | Isz : Felt → Op
  | Inv : Felt → Op
  | AndEqz : Expression Constraint → Expression Felt → Op
  | AndCond : Constraint → Felt → Constraint → Op
  | Variable : String → Op

def Op.eval (state : State) (e : Op) : Lit :=
  match e with
  | Const x => .Val x
  | True => .Constraint (_root_.True)
  | Get buffer i _ => .Val (buffer.get i)
  | Sub x y => .Val (x - y)
  | Variable name => state.findD name (Lit.Val 0)
  | AndEqz c x => 
    match c with
    | (Literal c) => .Constraint (c ∧ x = 0)
  | _ => .Constraint False

def Op.assign (state : State) (e : Op) (name : String) : State :=
  state.insert name (Op.eval state e)

inductive Cirgen where
  | Sequence : Cirgen → Cirgen → Cirgen
  | Assign : String → Op → Cirgen
  -- Should this take a String?
  | Return : Op → Cirgen

def Cirgen.step (state : State) (op : Cirgen) : State × Option Lit :=
  match op with
  -- We may want to encode the index of the instruction in `State`, and then
  -- always assign to the index instead of using a name.
  | Assign e name => (Op.assign state e name, none)
  | Sequence a b => let (state', x) := Cirgen.step state a
                    match x with
                    | some x => (state', some x)
                    | none => Cirgen.step state' b
  | Return e => (state, Op.eval state e)

open Op Cirgen in
theorem Sub_AndEqz_is_if_is_zero (state : State) :
  ∀ x : Felt, Sequence (Assign "x-1" (Op.Sub x 1)) (Assign "(x-1)=0" (AndEqz True (Variable "x-1"))) := by sorry
