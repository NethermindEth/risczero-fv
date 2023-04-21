import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

namespace Risc0

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

def Map (α : Type) (β : Type) := α → Option β

-- A pair of append-only stacks of assignments. Basically, this is where we
-- store the evaluated value of the expression on each line.
structure State where
  felts : Map String Felt
  buffers : Map String (List Felt)
  constraints : Map String Prop

-- A parametrized Variable. In practice, α will be either `Felt` or `Prop` or `List Felt`.
inductive Variable (α : Type) :=
  | mk : String → Variable α

-- An operation from the cirgen (circuit generation) MLIR dialect.
inductive Op where
  | Const : Felt → Op
  | True : Op
  | Get : Variable (List Felt) → ℕ → Felt → Op
  | Set : List Felt → ℕ → Felt → Op
  | Sub : Felt → Felt → Op
  | Mul : Felt → Felt → Op
  | Isz : Felt → Op
  | Inv : Felt → Op
  | AndEqz : Variable Prop → Variable Felt → Op
  | AndCond : Variable Prop → Variable Felt → Variable Prop → Op

instance : Inhabited Lit := ⟨(Lit.Val (-42))⟩

-- Evaluate a circuit operation to get some kind of literal.
@[simp]
def Op.eval (state : State) (op : Op) : Lit :=
  match op with
  | Const x => .Val x
  | True => .Constraint (_root_.True)
  | Get buffer i _ => let ⟨j⟩ := buffer
                      match state.buffers j with
                        | .none => default
                        | .some v => .Val <| v.getD i (-42)
  | Sub x y => .Val (x - y)
  | AndEqz c x => let ⟨i⟩ := c
                  let ⟨j⟩ := x
                  match state.constraints i, state.felts j with
                    | .some c, .some x => .Constraint (c ∧ x = 0)
                    | _      , _       => .Constraint (42 = 42)
  | AndCond old cond inner =>
      let ⟨i⟩ := old
      let ⟨j⟩ := cond
      let ⟨k⟩ := inner
      match state.constraints i, state.felts j, state.constraints k with
        | .some old, .some cond, .some inner => .Constraint (if cond == 0 then old else old ∧ inner)
        | _        , _         , _           => .Constraint (42 = 42)
  | _ => .Constraint (42 = 42)

-- Evaluate `op` and push its literal value to the stack.
@[simp]
def Op.assign (state : State) (op : Op) : State :=
  match (Op.eval state op) with
  | .Val x => { state with felts := x :: state.felts }
  | .Constraint c => { state with constraints := c :: state.constraints }

-- An MLIR program in the `cirgen` (circuit generation) dialect.
inductive Cirgen where
  | Assign : Op → Cirgen
  | Return : ℕ → Cirgen
  | Sequence : Cirgen → Cirgen → Cirgen

-- Step through the entirety of a `Cirgen` MLIR program from initial state
-- `state`, yielding the post-execution state and possibly a constraint
-- (`Prop`).
@[simp]
def Cirgen.step (state : State) (program : Cirgen) : State × Option Prop :=
  match program with
  | Assign op => (Op.assign state op, none)
  | Sequence a b => let (state', x) := Cirgen.step state a
                    match x with
                    | some x => (state', some x)
                    | none => Cirgen.step state' b
  | Return i => (state, some $ state.constraints.getD i False)

-- The result of stepping through a program that generates `(1 - x) = 0`, which
-- should be equivalent to checking `x = 1`.
def subAndEqzActual (x : Felt) : State × Option Prop :=
  Cirgen.step { felts := [], buffers := [], constraints := [] }
    (.Sequence
      (.Sequence
        (.Assign (Op.Sub x 1))
        (.Assign (.AndEqz (.Literal _root_.True) (.Variable 0))))
      (.Return 0))

-- The expected post-execution state after computing `subAndEqzActual`.
def subAndEqzExpectedState (x : Felt) : State :=
  { felts := [x - 1]
  , buffers := []
  , constraints := [x - 1 = 0]
  }

-- Check that our `(1 - x) = 0` program is equivalent to `x = 1`.
theorem Sub_AndEqz_iff_eq_one :
  ∀ x : Felt, (subAndEqzActual x).1 = subAndEqzExpectedState x
    ∧ (((subAndEqzActual x).2 = some c) → (c ↔ x = 1)) := by
  intros x
  apply And.intro
  unfold subAndEqzActual
  unfold subAndEqzExpectedState
  simp only [Cirgen.step, Op.assign, Op.eval, List.getD_cons_zero, true_and]
  intros h
  unfold subAndEqzActual at h
  simp only [Cirgen.step, Op.assign, Op.eval, List.getD_cons_zero, true_and, Option.some.injEq, eq_iff_iff] at h
  rw [← h]
  clear h
  apply Iff.intro
  simp only [and_false, List.getD_cons_zero, IsEmpty.forall_iff]
  intros h
  rw [sub_eq_zero] at h
  exact h
  intros h
  rw [h]
  simp only [List.getD_cons_zero]

def is0ConstraintsProgram (x : Felt) (y : Felt) (z : Felt) : State × Option Prop :=
  Cirgen.step { felts := [], buffers := [[x], [y, z]], constraints := [] }
  (.Sequence
    (.Sequence
      (.Sequence
        (.Sequence
          (.Sequence
            (.Sequence
              (.Assign (Op.Const 0))
              (.Assign Op.True))
              (.Assign (Op.Get (.Variable 0) 0 0)))
              (.Assign (Op.Get (.Variable 1) 0 0)))
              (.Assign (Op.AndEqz (.Variable 0) (.Variable 1))))
              (.Assign (Op.AndCond (.Variable 0) (.Variable 1) (.Variable 1))))
              (.Return 3))

end Risc0