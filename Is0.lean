import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs

@[inline]
def P: ℕ := 15 * 2^27 + 1

axiom P_prime: Nat.Prime P 
instance : Fact (Nat.Prime P) := ⟨P_prime⟩

-- A finite field element.
abbrev Felt := ZMod P

-- A literal, either a finite field element or a constraint.
inductive Lit where
  | Val : Felt → Lit
  | Constraint : Prop → Lit

-- A mapping of variable names to values.
--
-- Note: we can have duplicate keys if one maps to a felt and the other to a
-- constraint...
structure State where
  felts : Std.RBMap String Felt cmp
  constraints : Std.RBMap String Prop cmp

-- A parametrized expression. In practice, α will be either `Felt` or `Prop`.
inductive Expression (α : Type) where
  | Literal : α → Expression α
  | Variable : String → Expression α

-- An operation from the cirgen (circuit generation) MLIR dialect.
inductive Op where
  | Const : Felt → Op
  | True : Op
  | Get : Vector Felt n → Fin n → Felt → Op
  | Set : Vector Felt n → Fin n → Felt → Op
  | Sub : Felt → Felt → Op
  | Mul : Felt → Felt → Op
  | Isz : Felt → Op
  | Inv : Felt → Op
  | AndEqz : Expression Prop → Expression Felt → Op
  | AndCond : Prop → Felt → Prop → Op
  | Variable : String → Op

-- Evaluate a circuit operation to get some kind of literal.
def Op.eval (state : State) (op : Op) : Lit :=
  match op with
  | Const x => .Val x
  | True => .Constraint (_root_.True)
  | Get buffer i _ => .Val (buffer.get i)
  | Sub x y => .Val (x - y)
  | Variable name => .Val (state.felts.findD name 0)
  | AndEqz c x =>
    match c with
    | .Literal c => .Constraint (c ∧ x = .Literal 0)
    | .Variable name =>  .Constraint ((state.constraints.findD name _root_.True) ∧ x = .Literal 0)
  | _ => .Constraint False

-- Evaluate `op` and assign its value to `name` in the `state` context.
def Op.assign (state : State) (op : Op) (name : String) : State :=
  match (Op.eval state op) with
  | .Val x => { state with felts := state.felts.insert name x }
  | .Constraint c => { state with constraints := state.constraints.insert name c }

-- An MLIR program in the `cirgen` (circuit generation) dialect.
inductive Cirgen where
  | Sequence : Cirgen → Cirgen → Cirgen
  | Assign : String → Op → Cirgen
  | Return : String → Cirgen

-- Step through the entirety of a `Cirgen` MLIR program from initial state
-- `state`, yielding the post-execution state and possibly a constraint
-- (`Prop`).
def Cirgen.step (state : State) (program : Cirgen) : State × Option Prop :=
  match program with
  -- We may want to encode the index of the instruction in `State`, and then
  -- always assign to the index instead of using a name.
  | Assign name op => (Op.assign state op name, none)
  | Sequence a b => let (state', x) := Cirgen.step state a
                    match x with
                    | some x => (state', some x)
                    | none => Cirgen.step state' b
  | Return name => (state, some $ state.constraints.findD name _root_.True)

-- The result of stepping through a program that generates `(1 - x) = 0`, which
-- should be equivalent to checking `x = 1`.
def subAndEqzActual (x : Felt) : State × Option Prop :=
  Cirgen.step { felts := Std.RBMap.empty, constraints := Std.RBMap.empty }
    (.Sequence
      (.Sequence
        (.Assign "x-1" (Op.Sub x 1))
        (.Assign "(x-1)=0"
          (.AndEqz (.Literal _root_.True) (.Variable "x-1"))))
      (.Return "(x-1)=0"))

-- The expected post-execution state after computing `subAndEqzActual`.
def subAndEqzExpectedState (x : Felt) : State :=
  { felts := Std.RBMap.ofList [("x-1", x - 1)] cmp
  , constraints := Std.RBMap.ofList [("(x-1)=0", x - 1 = (0 : Felt))] cmp
  }

-- Check that our `(1 - x) = 0` program is equivalent to `x = 1`.
theorem Sub_AndEqz_iff_eq_one :
  ∀ x : Felt, (subAndEqzActual x).1 = subAndEqzExpectedState x
    ∧ (((subAndEqzActual x).2 = some c) → (c ↔ x = 1)) := by
  intros x
  apply And.intro
  sorry
  intros h
  unfold subAndEqzActual at h
  rw [Prod.snd] at h
  unfold Cirgen.step at h
  unfold Cirgen.step at h
  unfold Cirgen.step at h
  unfold Cirgen.step at h
  simp only at h
  rw [Option.some_inj] at h
  rw [← h]
  clear h
  apply Iff.intro
  unfold Op.assign
  unfold Op.eval
  simp only [and_false]
