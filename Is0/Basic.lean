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

-- A functional map, used to send variable names to literal values.
def Map (α : Type) (β : Type) := α → Option β

@[simp]
def Map.empty {α : Type} {β : Type} : Map α β := λ _ => none

@[simp]
def Map.update {α : Type} [BEq α] {β : Type} (m : Map α β) (k : α) (v : β) : Map α β :=
  λ x => if x == k then v else m x

@[simp]
def Map.fromList {α : Type} [BEq α] {β : Type} (l : List (α × β)) : Map α β :=
  match l with
  | [] => Map.empty
  | (k, v) :: xs => Map.update (Map.fromList xs) k v

-- The first three fields map variable names to values. The last is an
-- append-only stack of the constraints that we `Eqz`-ed.
structure State where
  felts : Map String Felt
  props : Map String Prop
  buffers : Map String (List Felt)
  constraints : List Prop

@[simp]
def State.update (state : State) (name : String) (x : Lit) : State :=
  match x with
  | .Val x => { state with felts := state.felts.update name x }
  | .Constraint c => { state with props := state.props.update name c }

@[simp]
lemma State.felts_collapsible
  {felts : Map String Felt}
  {props : Map String Prop}
  {buffers : Map String (List Felt)}
  {constraints : List Prop}
  (name : String) :
  State.felts { felts := felts, props := props, buffers := buffers, constraints := constraints } name = felts name := by
    exact rfl

@[simp]
lemma State.buffers_collapsible
  {felts : Map String Felt}
  {props : Map String Prop}
  {buffers : Map String (List Felt)}
  {constraints : List Prop}
  (name : String) :
  State.buffers { felts := felts, props := props, buffers := buffers, constraints := constraints } name = buffers name := by
    exact rfl

-- A parametrized Variable. In practice, α will be one of `Felt`, `Prop`, or `List Felt`.
inductive Variable (α : Type) :=
  | mk : String → Variable α

-- Pure functional operations from the cirgen (circuit generation) MLIR dialect.
inductive Op where
  | Const : Felt → Op
  | True : Op
  | Get : Variable (List Felt) → ℕ → Felt → Op
  | Sub : Variable Felt → Variable Felt → Op
  | Mul : Variable Felt → Variable Felt → Op
  | Isz : Variable Felt → Op
  | Inv : Variable Felt → Op
  | AndEqz : Variable Prop → Variable Felt → Op
  | AndCond : Variable Prop → Variable Felt → Variable Prop → Op

instance : Inhabited Lit := ⟨(Lit.Val (-42))⟩

-- Evaluate a pure functional circuit operation to get some kind of literal.
def Op.eval (state : State) (op : Op) : Lit :=
  match op with
  | Const x => .Val x
  | True => .Constraint (_root_.True)
  | Get buffer i _ => let ⟨j⟩ := buffer
                      match state.buffers j with
                        | some v => .Val <| v.getD i (-42)
                        | _      => default
  | Sub x y => let ⟨i⟩ := x
               let ⟨j⟩ := y
               .Val $ match state.felts i, state.felts j with
                 | some x, some y => x - y
                 | _      , _       => 42
  | Mul x y => let ⟨i⟩ := x
               let ⟨j⟩ := y
               .Val $ match state.felts i, state.felts j with
                 | some x, some y => x * y
                 | _      , _       => 42
  | AndEqz c x => let ⟨i⟩ := c
                  let ⟨j⟩ := x
                  match state.props i, state.felts j with
                    | some c, some x => .Constraint (c ∧ x = 0)
                    | _      , _       => .Constraint (42 = 42)
  | AndCond old cond inner =>
      let ⟨i⟩ := old
      let ⟨j⟩ := cond
      let ⟨k⟩ := inner
      match state.props i, state.felts j, state.props k with
        | .some old, .some cond, .some inner => .Constraint (if cond == 0 then old else old ∧ inner)
        | _        , _         , _           => .Constraint (42 = 42)
  | Isz x => let ⟨i⟩ := x
             match state.felts i with
             | some x => .Val $ if x == 0 then 1 else 0
             | _      => .Val 42
  | Inv x => let ⟨i⟩ := x
             match state.felts i with
             | some x => .Val $ if x == 0 then 0 else x⁻¹
             | _      => .Val 42

-- Evaluate `op` and map `name ↦ result` in `state : State`.
def Op.assign (state : State) (op : Op) (name : String) : State :=
  match (Op.eval state op) with
  | .Val x => { state with felts := state.felts.update name x }
  | .Constraint c => { state with props := state.props.update name c }

-- An MLIR program in the `cirgen` (circuit generation) dialect. MLIR ops that
-- are not pure functions are implemented here, so they can mess with state. 
inductive Cirgen where
  | If : Variable Felt → Cirgen → Cirgen
  | Eqz : Variable Felt → Cirgen
  | Set : Variable (List Felt) → ℕ → Variable Felt → Cirgen
  | Return : String → Cirgen
  | Assign : String → Op → Cirgen
  | Sequence : Cirgen → Cirgen → Cirgen

-- Step through the entirety of a `Cirgen` MLIR program from initial state
-- `state`, yielding the post-execution state and possibly a constraint
-- (`Prop`), the return value of the program.
def Cirgen.step (state : State) (program : Cirgen) : State × Option Prop :=
  match program with
  | If x program =>
    let ⟨name⟩ := x
    match state.felts name with
      | .some x => if x == 0
                   then (state, none)
                   else Cirgen.step state program
      | none    => (state, 42 = 42)
  | Eqz x =>
    let ⟨name⟩ := x
    match state.felts name with
      | .some x => ({ state with constraints := (x = 0) :: state.constraints }, none)
      | .none   => (state, 42 = 42)
  | Set buffer i x =>
    let ⟨name⟩ := buffer
    let ⟨nameₓ⟩ := x
      match state.buffers name, state.felts nameₓ with
        | .some buffer, .some x =>
          let buffers' := state.buffers.update name (buffer.set i x)
          ({state with buffers := buffers' }, none)
        | _, _ => (state, none)
  | Assign name op => (Op.assign state op name, none)
  | Sequence a b => let (state', x) := Cirgen.step state a
                    match x with
                      | some x => (state', some x)
                      | none => Cirgen.step state' b
  | Return name => let retval:=
                    match state.props name with
                    | some retval => retval
                    | none => 42 = 42
                   (state, some retval)

-- The result of stepping through a program that generates `(1 - x) = 0`, which
-- should be equivalent to checking `x = 1`.
def subAndEqzActual (x : Felt) : State × Option Prop :=
  Cirgen.step { felts := Map.empty, buffers := Map.empty, props := Map.empty, constraints := [] }
    (.Sequence
      (.Sequence
        (.Sequence
          (.Sequence
            (.Sequence
              (.Assign "1" (Op.Const 1))
              (.Assign "x" (Op.Const x)))
              (.Assign "true" (Op.True)))
              (.Assign "x - 1" (Op.Sub ⟨"x"⟩ ⟨"1"⟩)))
              (.Assign "x - 1 = 0" (.AndEqz (⟨"true"⟩) (⟨"x - 1"⟩))))
              (.Return "x - 1 = 0"))

-- The expected post-execution state after computing `subAndEqzActual`.
def subAndEqzExpectedState (x : Felt) : State :=
  { felts := Map.fromList [("x - 1", x - 1), ("x", x), ("1", 1)]
  , props := Map.fromList [("x - 1 = 0", x - 1 = 0), ("true", True)]
  , buffers := Map.empty
  , constraints := []
  }

-- Check that our `(1 - x) = 0` program is equivalent to `x = 1`.
theorem Sub_AndEqz_iff_eq_one :
  ∀ x : Felt, (subAndEqzActual x).1 = subAndEqzExpectedState x
    ∧ (((subAndEqzActual x).2 = some c) → (c ↔ x = 1)) := by
  intros x
  unfold subAndEqzActual
  apply And.intro
  unfold subAndEqzExpectedState
  simp only [Cirgen.step, Op.assign, Op.eval, Map.update, beq_iff_eq, Map.empty, ite_false, ite_true, true_and, Map.fromList, State.mk.injEq]
  simp only [Cirgen.step, Op.assign, Op.eval, Map.update, beq_iff_eq, Map.empty, ite_false, ite_true, true_and, Option.some.injEq, eq_iff_iff]
  intros h
  rw [←h]
  clear h
  apply Iff.intro
  intros h₁
  rw [sub_eq_zero] at h₁
  exact h₁
  intros h₂
  rw [h₂]
  decide

end Risc0
