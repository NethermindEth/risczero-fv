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

@[simp]
lemma State.if_output {state₁ state₂ : State} {x : Felt} :
  (if (x = 0) then state₁ else state₂).output = if (x = 0) then state₁.output else state₂.output := by
  exact apply_ite output (x = 0) state₁ state₂

notation:61 st "[" n:61 "]" " := " x:49 => State.update st n x

-- A parametrized Variable. In practice, α will be one of `Felt`, `Prop`, or `List Felt`.
structure Variable (α : Type) :=
  name : String

inductive IsNondet :=
  | InNondet
  | NotInNondet

open IsNondet

@[reducible]
def lub (x₁ x₂ : IsNondet) :=
  match x₁ with
    | InNondet => InNondet
    | _ => x₂

-- Pure functional operations from the cirgen (circuit generation) MLIR dialect.
inductive Op : IsNondet → Type where
  | Const : Felt → Op x
  | True : Op x
  | GetInput : ℕ → Felt → Op x
  | GetOutput : ℕ → Felt → Op x
  | Sub : Variable Felt → Variable Felt → Op x
  | Mul : Variable Felt → Variable Felt → Op x
  | AndEqz : Variable Prop → Variable Felt → Op x
  | AndCond : Variable Prop → Variable Felt → Variable Prop → Op x
  | Isz : Variable Felt → Op InNondet
  | Inv : Variable Felt → Op InNondet

open Op

instance {x : IsNondet} : HSub (Variable Felt) (Variable Felt) (Op x) := ⟨Op.Sub⟩
instance {x : IsNondet} : HMul (Variable Felt) (Variable Felt) (Op x) := ⟨Op.Mul⟩

-- Notation for Ops.
namespace MLIRNotation

scoped prefix:max "C" => Op.Const
scoped notation:max "⊤" => Op.True
scoped notation:max "input[" n "]" => Op.GetInput n 0
scoped notation:max "output[" n "]" => Op.GetOutput n 0
scoped infix:55 " &₀ " => Op.AndEqz
scoped notation:55 " guard " c " & " x " with " y:55 => Op.AndCond x c y
scoped prefix:57 "??₀" => Op.Isz
scoped prefix:max "Inv" => Op.Inv

end MLIRNotation

-- Evaluate a pure functional circuit operation to get some kind of literal.
def Op.eval {x} (state : State) (op : Op x) : Lit :=
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

notation:61 "Γ " st:max " ⟦" p:49 "⟧ₑ" => Op.eval st p

inductive MLIR : IsNondet → Type where
  | Assign : String → Op x → MLIR x
  | Eqz : Variable Felt → MLIR x
  | If : Variable Felt → MLIR x → MLIR x
  | Nondet : MLIR InNondet → MLIR NotInNondet
  | Sequence : MLIR x → MLIR x → MLIR x
  | SetOutput : Variable Felt → Op x → MLIR InNondet

-- Notation for MLIR programs.  
namespace MLIRNotation

scoped infix:51 "←ₐ " => MLIR.Assign
scoped prefix:52 "?₀" => MLIR.Eqz
scoped notation:51 "guard " c " then " x:51 => MLIR.If c x
scoped prefix:max "nondet" => MLIR.Nondet
scoped infixr:50 "; " => MLIR.Sequence
scoped notation:51 (priority := high) "output[" v:51 "]" " ←ᵢ " x:51 => MLIR.SetOutput v x

end MLIRNotation

abbrev MLIRProgram := MLIR NotInNondet

-- open MLIR in
-- lemma x : MLIRProgram := Sequence (Nondet (Assign "x" (Op.Isz ⟨"y"⟩))) (Assign "z" (Op.Const 4))

-- open MLIR in
-- lemma y : MLIR InNondet := Sequence ((Assign "x" (Op.Isz ⟨"y"⟩))) ((Assign "z" (Op.Const 4)))

namespace MLIRNotation

-- scoped notation:56 (priority := high) "[" x "]" => ⟨x⟩

end MLIRNotation

-- instance : Inhabited Lit := ⟨(Lit.Val (-42))⟩

namespace Op

section Op

open MLIRNotation

variable (st : State) {α : IsNondet}

@[simp]
lemma eval_const {x : Felt} : Γ st ⟦@Const α x⟧ₑ = .Val x := rfl

@[simp]
lemma eval_true : Γ st ⟦@Op.True α⟧ₑ = .Constraint (_root_.True) := rfl

@[simp]
lemma eval_getInput {i : ℕ} {x : Felt} : Γ st ⟦@GetInput α i x⟧ₑ = .Val (st.input.getD i (-42)) := rfl

@[simp]
lemma eval_getOutput {i : ℕ} {x : Felt} : Γ st ⟦@GetOutput α i x⟧ₑ = .Val (st.output.getD i (-42)) := rfl

@[simp]
lemma eval_sub {x y : Variable Felt} :
  Γ st ⟦@Sub α x y⟧ₑ = .Val (match st.felts x.name, st.felts y.name with
                              | some x, some y => x - y
                              | _      , _     => 42) := rfl

@[simp]
lemma eval_mul {x y : Variable Felt} :
  Γ st ⟦@Mul α x y⟧ₑ = .Val (match st.felts x.name, st.felts y.name with
                              | some x, some y => x * y
                              | _      , _     => 42) := rfl

@[simp]
lemma eval_isz {x : Variable Felt} :
  Γ st ⟦??₀x⟧ₑ = .Val (match st.felts x.name with
                        | some x => if x == 0 then 1 else 0
                        | _      => 42) := rfl
@[simp]
lemma eval_inv {x : Variable Felt} :
  Γ st ⟦Inv x⟧ₑ = .Val (match st.felts x.name with
                         | some x => if x == 0 then 0 else x⁻¹
                         | _      => 42) := rfl

-- lemma eval_eqz {c : Variable Prop}
--                {x : Variable Felt}
--     (h₁ : state.props c.name = some c₁)
--     (h₂ : state.felts x.name = some x₁) :
--   (AndEqz c x).eval state = .Constraint (c₁ ∧ x₁ = 0) := by simp [eval, *]

@[simp]
lemma eval_andEqz :
  Γ st ⟦@AndEqz α c x⟧ₑ =
    .Constraint (match st.props c.name, st.felts x.name with
                   | some c, some x => (c ∧ x = 0)
                   | _      , _     => (42 = 42)) := rfl

@[simp]
lemma eval_andCond :
  Γ st ⟦@AndCond α old cnd inner⟧ₑ =
    .Constraint (match st.props old.name, st.felts cnd.name, st.props inner.name with
                  | .some old, .some cnd, .some inner => if cnd == 0 then old else old ∧ inner
                  | _        , _         , _           => 42 = 42) := rfl

end Op

end Op

-- -- Evaluate `op` and map `name ↦ result` in `state : State`.
-- def Op.assign (state : State) (op : Op) (name : String) : State :=
--   match (Op.eval state op) with
--   | .Val x => { state with felts := state.felts.update name x }
--   | .Constraint c => { state with props := state.props.update name c }

-- -- An MLIR program in the `cirgen` (circuit generation) dialect. MLIR ops that
-- -- are not pure functions are implemented here, so they can mess with state. 
-- inductive MLIR where
--   | If : Variable Felt → MLIR → MLIR
--   | Eqz : Variable Felt → MLIR
--   | Assign : String → Op → MLIR
--   | Sequence : MLIR → MLIR → MLIR
--   | SetInput : ℕ → Variable Felt → MLIR
--   | SetOutput : ℕ → Variable Felt → MLIR

-- namespace MLIRNotation

-- -- Notation for MLIR programs.
-- scoped infixr:50 "; " => MLIR.Sequence
-- scoped infix:51 "←ₐ " => MLIR.Assign
-- scoped notation:51 (priority := high) "input[" v:51 "]" " ←ᵢ " x:51 => MLIR.SetInput v x
-- scoped notation:51 (priority := high) "output[" v:51 "]" " ←ᵢ " x:51 => MLIR.SetOutput v x
-- scoped notation:51 "guard " c " then " x:51 => MLIR.If c x
-- scoped prefix:52 "?₀" => MLIR.Eqz
-- -- scoped prefix:max "ret" => MLIR.Return

-- end MLIRNotation
-- -- Step through the entirety of a `MLIR` MLIR program from initial state
-- -- `state`, yielding the post-execution state and possibly a constraint
-- -- (`Prop`), the return value of the program.
-- def MLIR.run (state : State) (program : MLIR) : State :=
--   match program with
--   | If x program =>
--     match state.felts x.name with
--       | .some x => if x == 0
--                    then state
--                    else MLIR.run state program
--       | none    => state
--   | Eqz x =>
--     match state.felts x.name with
--       | .some x => {state with constraints := (x = 0) :: state.constraints}
--       | .none   => state
--   | SetInput i x =>
--       match state.felts x.name with
--         | .some x => {state with input := state.input.set i x}
--         | _       => state
--   | SetOutput i x =>
--       match state.felts x.name with
--         | .some x => {state with output := state.output.set i x}
--         | _       => state
--   | Assign name op => Op.assign state op name
--   | Sequence a b => let state' := MLIR.run state a
--                     MLIR.run state' b
  
-- notation:61 "Γ " st:max " ⟦" p:49 "⟧" => MLIR.run st p

-- lemma run_setOutput_of_some
--   {state : State}
--   {i : ℕ}
--   {x₁ : Felt}
--   {x : Variable Felt}
--   (h : state.felts x.name = some x₁) :
--   Γ state ⟦MLIR.SetOutput i x⟧ = {state with output := state.output.set i x₁} := by simp [MLIR.run, h]

-- lemma run_Eqz_of_some
--   {state : State}
--   {x₁ : Felt}
--   {x : Variable Felt}
--   (h : state.felts x.name = some x₁) :
--   Γ state ⟦MLIR.Eqz x⟧ = {state with constraints := (x₁ = 0) :: state.constraints } := by simp [MLIR.run, h]

end Risc0
