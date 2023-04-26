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

namespace Map

section Map

variable {α : Type} [BEq α] [DecidableEq α] {β : Type}

def empty : Map α β := λ _ => none

def update (m : Map α β) (k : α) (v : β) : Map α β :=
  λ x => if x = k then v else m x

def fromList (l : List (α × β)) : Map α β :=
  match l with
  | [] => Map.empty
  | (k, v) :: xs => Map.update (Map.fromList xs) k v

notation:61 st "[" n:61 "]" " := " x:49 => Map.update st n x

@[simp]
lemma fromList_nil : fromList ([] : List (α × β)) = Map.empty := rfl

@[simp]
lemma fromList_cons {k : α} {v : β} {l : List (α × β)} :
  fromList ((k, v) :: l) = Map.update (Map.fromList l) k v := rfl

@[simp]
lemma update_get {m : Map α β} {k : α} {v : β} :
  (m[k] := v) k = v := by simp [update]

lemma update_update_get {m : Map α β} {k k' : α} {v v' : β} (h : k ≠ k') :
  ((m[k] := v)[k'] := v') k = some v := by
  unfold update
  simp [*]

lemma update_get' {m : Map α β} {k k' : α} {v' : β}
  (v : β) (h : k ≠ k') (h₁ : m k = some v) :
  (m[k'] := v') k = some v := by simp [update, *]

end Map

end Map

-- The first three fields map variable names to values. The last is an
-- append-only stack of the expressions we assert are equal to zero via `Eqz`.
structure State where
  felts : Map String Felt
  props : Map String Prop
  input : List Felt
  output : List Felt
  constraints : List Prop

def State.update (state : State) (name : String) (x : Lit) : State :=
  match x with
  | .Val x => { state with felts := state.felts.update name x }
  | .Constraint c => { state with props := state.props.update name c }

@[simp]
lemma State.update_val {state : State} {name : String} {x : Felt} :
  update state name (.Val x) = { state with felts := state.felts.update name x } := rfl

@[simp]
lemma State.update_constraint {state : State} {name : String} {c : Prop} :
  update state name (.Constraint c) = { state with props := state.props.update name c } := rfl

@[simp]
lemma State.if_constraints {state₁ state₂ : State} {x : Felt} :
  (if (x = 0) then state₁ else state₂).constraints = if (x = 0) then state₁.constraints else state₂.constraints := by
  exact apply_ite constraints (x = 0) state₁ state₂

notation:61 st "[" n:61 "]" " := " x:49 => State.update st n x

-- A parametrized Variable. In practice, α will be one of `Felt`, `Prop`, or `List Felt`.
structure Variable (α : Type) :=
  name : String

-- Pure functional operations from the cirgen (circuit generation) MLIR dialect.
inductive Op where
  | Const : Felt → Op
  | True : Op
  | GetInput : ℕ → Felt → Op
  | GetOutput : ℕ → Felt → Op
  | Sub : Variable Felt → Variable Felt → Op
  | Mul : Variable Felt → Variable Felt → Op
  | Isz : Variable Felt → Op
  | Inv : Variable Felt → Op
  | AndEqz : Variable Prop → Variable Felt → Op
  | AndCond : Variable Prop → Variable Felt → Variable Prop → Op

namespace MLIRNotation

-- scoped notation:56 (priority := high) "[" x "]" => ⟨x⟩

end MLIRNotation

-- Notation for Ops.
namespace MLIRNotation

scoped infix:55 " &₀ " => Op.AndEqz
scoped notation:55 " guard " c " & " x " with " y:55 => Op.AndCond x c y
scoped prefix:max "C" => Op.Const
scoped notation:max "⊤" => Op.True
scoped notation:max "input[" n "]" => Op.GetInput n 0
scoped notation:max "output[" n "]" => Op.GetOutput n 0
scoped prefix:57 "??₀" => Op.Isz
scoped prefix:max "Inv" => Op.Inv

-- scoped prefix:max "C" => Op.Const


end MLIRNotation

instance : Inhabited Lit := ⟨(Lit.Val (-42))⟩

-- Evaluate a pure functional circuit operation to get some kind of literal.
def Op.eval (state : State) (op : Op) : Lit :=
  match op with
  | Const x => .Val x
  | True => .Constraint (_root_.True)
  | GetInput i _ => .Val <| state.input.getD i (-42)
  | GetOutput i _ => .Val <| state.output.getD i (-42)
  | Sub x y => .Val $ match state.felts x.name, state.felts y.name with
                        | some x, some y => x - y
                        | _      , _       => 42
  | Mul x y => .Val $ match state.felts x.name, state.felts y.name with
                        | some x, some y => x * y
                        | _      , _       => 42
  | AndEqz c x => .Constraint $ match state.props c.name, state.felts x.name with
                    | some c, some x => c ∧ x = 0
                    | _      , _     => 42 = 42
  | AndCond old cond inner =>
      .Constraint $ match state.props old.name, state.felts cond.name, state.props inner.name with
        | .some old, .some cond, .some inner => if cond == 0 then old else old ∧ inner
        | _        , _         , _           => 42 = 42
  | Isz x => .Val $ match state.felts x.name with
               | some x => if x == 0 then 1 else 0
               | _      => 42
  | Inv x => .Val $ match state.felts x.name with
               | some x => if x == 0 then 0 else x⁻¹
               | _      => 42

namespace Op

section Op

variable (state : State) (op : Op)

@[simp]
lemma eval_const {x : Felt} : Op.eval state (Const x) = .Val x := by rfl

@[simp]
lemma eval_const_one : Op.eval state (Const 1 : Op) = .Val 1 := by rfl

@[simp]
lemma eval_true : Op.eval state True = .Constraint (_root_.True) := by rfl

@[simp]
lemma eval_getInput {i : ℕ} {x : Felt} : Op.eval state (GetInput i x) = .Val (state.input.getD i (-42)) := by rfl

@[simp]
lemma eval_getOutput {i : ℕ} {x : Felt} : Op.eval state (GetOutput i x) = .Val (state.output.getD i (-42)) := by rfl

@[simp]
lemma eval_sub {x : Variable Felt} {y : Variable Felt} :
  Op.eval state (Sub x y) = .Val (match state.felts x.name, state.felts y.name with
                                      | some x, some y => x - y
                                      | _      , _       => 42) := by rfl
 
@[simp]
lemma eval_mul {x : Variable Felt} {y : Variable Felt} :
  Op.eval state (Mul x y) = .Val (match state.felts x.name, state.felts y.name with
                                      | some x, some y => x * y
                                      | _      , _       => 42) := by rfl

@[simp]
lemma eval_isz {x : Variable Felt} :
  Op.eval state (Isz x) = .Val (match state.felts x.name with
                                  | some x => if x == 0 then 1 else 0
                                  | _      => 42) := by rfl
@[simp]
lemma eval_inv {x : Variable Felt} :
  Op.eval state (Inv x) = .Val (match state.felts x.name with
                                  | some x => if x == 0 then 0 else x⁻¹
                                  | _      => 42) := by rfl

-- lemma eval_eqz {c : Variable Prop}
--                {x : Variable Felt}
--     (h₁ : state.props c.name = some c₁)
--     (h₂ : state.felts x.name = some x₁) :
--   (AndEqz c x).eval state = .Constraint (c₁ ∧ x₁ = 0) := by simp [eval, *]

@[simp]
lemma eval_andEqz :
  (AndEqz c x).eval state =
    .Constraint (match state.props c.name, state.felts x.name with
                 | some c, some x => (c ∧ x = 0)
                 | _      , _     => (42 = 42)) := rfl

@[simp]
lemma eval_andCond :
  (AndCond old cnd inner).eval state =
    .Constraint (match state.props old.name, state.felts cnd.name, state.props inner.name with
        | .some old, .some cnd, .some inner => if cnd == 0 then old else old ∧ inner
        | _        , _         , _           => 42 = 42) := rfl

end Op

end Op

-- Evaluate `op` and map `name ↦ result` in `state : State`.
def Op.assign (state : State) (op : Op) (name : String) : State :=
  match (Op.eval state op) with
  | .Val x => { state with felts := state.felts.update name x }
  | .Constraint c => { state with props := state.props.update name c }

-- An MLIR program in the `cirgen` (circuit generation) dialect. MLIR ops that
-- are not pure functions are implemented here, so they can mess with state. 
inductive MLIR where
  | If : Variable Felt → MLIR → MLIR
  | Eqz : Variable Felt → MLIR
  | Assign : String → Op → MLIR
  | Sequence : MLIR → MLIR → MLIR
  | SetInput : ℕ → Variable Felt → MLIR
  | SetOutput : ℕ → Variable Felt → MLIR

namespace MLIRNotation

-- Notation for MLIR programs.
scoped infixr:50 "; " => MLIR.Sequence
scoped infix:51 "←ₐ " => MLIR.Assign
scoped notation:51 (priority := high) "input[" v:51 "]" " ←ᵢ " x:51 => MLIR.SetInput v x
scoped notation:51 (priority := high) "output[" v:51 "]" " ←ᵢ " x:51 => MLIR.SetOutput v x
scoped notation:51 "guard " c " then " x:51 => MLIR.If c x
scoped prefix:52 "?₀" => MLIR.Eqz
-- scoped prefix:max "ret" => MLIR.Return

end MLIRNotation
-- Step through the entirety of a `MLIR` MLIR program from initial state
-- `state`, yielding the post-execution state and possibly a constraint
-- (`Prop`), the return value of the program.
def MLIR.run (state : State) (program : MLIR) : State :=
  match program with
  | If x program =>
    match state.felts x.name with
      | .some x => if x == 0
                   then state
                   else MLIR.run state program
      | none    => state
  | Eqz x =>
    match state.felts x.name with
      | .some x => {state with constraints := (x = 0) :: state.constraints}
      | .none   => state
  | SetInput i x =>
      match state.felts x.name with
        | .some x => {state with input := state.input.set i x}
        | _       => state
  | SetOutput i x =>
      match state.felts x.name with
        | .some x => {state with output := state.output.set i x}
        | _       => state
  | Assign name op => Op.assign state op name
  | Sequence a b => let state' := MLIR.run state a
                    MLIR.run state' b
  
notation:61 "Γ " st:max " ⟦" p:49 "⟧" => MLIR.run st p

lemma run_setOutput_of_some
  {state : State}
  {i : ℕ}
  {x₁ : Felt}
  {x : Variable Felt}
  (h : state.felts x.name = some x₁) :
  Γ state ⟦MLIR.SetOutput i x⟧ = {state with output := state.output.set i x₁} := by simp [MLIR.run, h]

lemma run_Eqz_of_some
  {state : State}
  {x₁ : Felt}
  {x : Variable Felt}
  (h : state.felts x.name = some x₁) :
  Γ state ⟦MLIR.Eqz x⟧ = {state with constraints := (x₁ = 0) :: state.constraints } := by simp [MLIR.run, h]

end Risc0
