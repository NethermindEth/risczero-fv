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
  | Sub : Variable Felt → Variable Felt → Op
  | Mul : Variable Felt → Variable Felt → Op
  | Isz : Variable Felt → Op
  | Inv : Variable Felt → Op
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
  | Sub x y => let ⟨i⟩ := x
               let ⟨j⟩ := y
               .Val $ match state.felts i, state.felts j with
                 | .some x, .some y => x - y
                 | _      , _       => 42
  | Mul x y => let ⟨i⟩ := x
               let ⟨j⟩ := y
               .Val $ match state.felts i, state.felts j with
                 | .some x, .some y => x * y
                 | _      , _       => 42
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
def Op.assign (state : State) (op : Op) (name : String) : State :=
  match (Op.eval state op) with
  | .Val x => { state with felts := state.felts.update name x }
  | .Constraint c => { state with constraints := state.constraints.update name c }

-- An MLIR program in the `cirgen` (circuit generation) dialect.
inductive Cirgen where
  | If : Variable Felt → Cirgen → Cirgen
  | Eqz : Variable Felt → Cirgen
  | Set : Variable (List Felt) → ℕ → Variable Felt → Cirgen
  | Return : String → Cirgen
  | Assign : String → Op → Cirgen
  | Sequence : Cirgen → Cirgen → Cirgen

-- Step through the entirety of a `Cirgen` MLIR program from initial state
-- `state`, yielding the post-execution state and possibly a constraint
-- (`Prop`).
@[simp]
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
      | .some x => if x == 0
                   then (state, none)
                   else (state, some False)
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
                    match state.constraints name with
                    | some retval => retval
                    | none => 42 = 42
                   (state, some retval)

-- The result of stepping through a program that generates `(1 - x) = 0`, which
-- should be equivalent to checking `x = 1`.
def subAndEqzActual (x : Felt) : State × Option Prop :=
  Cirgen.step { felts := Map.empty, buffers := Map.empty, constraints := Map.empty }
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
  , buffers := Map.empty
  , constraints := Map.fromList [("x - 1 = 0", x - 1 = 0), ("true", True)]
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

def is0OriginalProgram (x : Felt) (y : Felt) (z : Felt) : State × Option Prop :=
  Cirgen.step { felts := Map.empty
              , buffers := Map.fromList [("in", [x]), ("out", [y, z])]
              , constraints := Map.empty
              }
    (.Sequence
      (.Sequence
        (.Sequence
          (.Sequence
            (.Sequence
              (.Sequence
                (.Sequence
                  (.Sequence
                    (.Sequence
                      (.Assign "1" (Op.Const 1))
                      (.Assign "x" (Op.Get ⟨"in"⟩ 0 0)))
                      (.Assign "isZeroBit" (Op.Isz ⟨"x"⟩)))
                      (.Set ⟨"out"⟩ 0 ⟨"isZeroBit"⟩))
                      (.Assign "invVal" (Op.Inv ⟨"x"⟩)))
                      (.Set ⟨"out"⟩ 1 ⟨"invVal"⟩))
                      (.Assign "out[0]" (Op.Get ⟨"out"⟩ 0 0)))
                      (.If ⟨"out[0]"⟩
                        (.Eqz ⟨"x"⟩)))
                      (.Assign "1 - out[0]" (Op.Sub ⟨"1"⟩ ⟨"out[0]"⟩)))
                      (.If ⟨"1 - out[0]"⟩
                        (.Sequence
                          (.Sequence
                            (.Sequence
                              (.Assign "out[1]" (Op.Get ⟨"out"⟩ 1 0))
                              (.Assign "x * out[1]" (Op.Mul ⟨"x"⟩ ⟨"out[1]"⟩)))
                              (.Assign "x * out[1] - 1" (Op.Sub ⟨"x * out[1]"⟩ ⟨"1"⟩)))
                              (.Eqz ⟨"x * out[1] - 1"⟩))))

def is0ConstraintsProgram (x : Felt) (y : Felt) (z : Felt) : State × Option Prop :=
  Cirgen.step { felts := Map.empty
              , buffers := Map.fromList [("in", [x]), ("out", [y, z])]
              , constraints := Map.empty
              }
  (.Sequence
    (.Sequence
      (.Sequence
        (.Sequence
          (.Sequence
            (.Sequence
              (.Sequence
                (.Sequence
                  (.Sequence
                    (.Sequence
                      (.Sequence
                        (.Sequence
                          (.Assign "1" (Op.Const 1))
                          (.Assign "true" Op.True))
                          (.Assign "x" (Op.Get ⟨"in"⟩ 0 0)))
                          (.Assign "isZeroBit" (Op.Get ⟨"out"⟩ 0 0)))
                          (.Assign "x = 0" (Op.AndEqz ⟨"true"⟩ ⟨"x"⟩)))
                          (.Assign "IF isZeroBit THEN (x = 0) ELSE true" (Op.AndCond ⟨"true"⟩ ⟨"isZeroBit"⟩ ⟨"x = 0"⟩)))
                          (.Assign "1 - isZeroBit" (Op.Sub ⟨"1"⟩ ⟨"isZeroBit"⟩)))
                          (.Assign "invVal" (Op.Get ⟨"out"⟩ 1 0)))
                          (.Assign "x * invVal" (Op.Mul ⟨"x"⟩ ⟨"invVal"⟩)))
                          (.Assign "x * invVal - 1" (Op.Sub ⟨"x * invVal"⟩ ⟨"1"⟩)))
                          (.Assign "x * invVal - 1 = 0" (Op.AndEqz ⟨"true"⟩ ⟨"x * invVal - 1"⟩)))
                          (.Assign "result"
                            (Op.AndCond
                              ⟨"IF isZeroBit THEN (x = 0) ELSE true"⟩
                              ⟨"1 - isZeroBit"⟩
                              ⟨"x * invVal - 1 = 0"⟩)))
                          (.Return "result"))

end Risc0
