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

variable {α : Type} [DecidableEq α] {β : Type}

def empty : Map α β := λ _ => none

def update (m : Map α β) (k : α) (v : β) : Map α β :=
  λ x => if x = k then v else m x

def fromList (l : List (α × β)) : Map α β :=
  match l with
  | [] => Map.empty
  | (k, v) :: xs => Map.update (Map.fromList xs) k v

notation:61 m "[" k:61 "]" " := " v:49 => Map.update m k v

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
  (if x = 0 then state₁ else state₂).constraints =
  if x = 0 then state₁.constraints else state₂.constraints := by apply apply_ite

@[simp]
lemma State.if_output {state₁ state₂ : State} {x : Felt} :
  (if x = 0 then state₁ else state₂).output =
  if (x = 0) then state₁.output else state₂.output := by apply apply_ite

notation:61 st "[" n:61 "]" " := " x:49 => State.update st n x

inductive VarType := | FeltTag | PropTag | ListFeltTag

structure Variable (tag : VarType) :=
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
open VarType in
inductive Op : IsNondet → Type where
  | Const : Felt → Op x
  | True : Op x
  | GetInput : ℕ → Felt → Op x
  | GetOutput : ℕ → Felt → Op x
  | Add : Variable FeltTag → Variable FeltTag → Op x
  | Sub : Variable FeltTag → Variable FeltTag → Op x
  | Mul : Variable FeltTag → Variable FeltTag → Op x
  | Pow : Variable FeltTag → ℕ → Op x
  | Neg : Variable FeltTag → Op x
  | AndEqz : Variable PropTag → Variable FeltTag → Op x
  | AndCond : Variable PropTag → Variable FeltTag → Variable PropTag → Op x
  | Isz : Variable FeltTag → Op InNondet
  | Inv : Variable FeltTag → Op InNondet

open Op VarType

instance {x : IsNondet} : HAdd (Variable FeltTag) (Variable FeltTag) (Op x) := ⟨Op.Add⟩
instance {x : IsNondet} : HSub (Variable FeltTag) (Variable FeltTag) (Op x) := ⟨Op.Sub⟩
instance {x : IsNondet} : HMul (Variable FeltTag) (Variable FeltTag) (Op x) := ⟨Op.Mul⟩
instance {x : IsNondet} : HPow (Variable FeltTag) ℕ                  (Op x) := ⟨Op.Pow⟩

-- Notation for Ops.
namespace MLIRNotation

scoped prefix:max "-" => Op.Neg
scoped prefix:max "C" => Op.Const
scoped notation:max "⊤" => Op.True
scoped notation:max "input[" n "]" => Op.GetInput n 0
scoped notation:max "output[" n "]" => Op.GetOutput n 0
scoped infix:55 " &₀ " => Op.AndEqz
scoped notation:55 " guard " c " & " x " with " y:55 => Op.AndCond x c y
scoped prefix:57 "??₀" => Op.Isz
scoped prefix:max "Inv" => Op.Inv

end MLIRNotation

instance : Inhabited Felt := ⟨-42⟩

-- Evaluate a pure functional circuit operation to get some kind of literal.
def Op.eval {x} (st : State) (op : Op x) : Lit :=
  match op with
  | Const x       => .Val x
  | True          => .Constraint _root_.True
  | GetInput i _  => .Val <| st.input.get! i
  | GetOutput i _ => .Val <| st.output.get! i
  | Add x y       => .Val <| (st.felts x.name).get! + (st.felts y.name).get!
  | Sub x y       => .Val <| (st.felts x.name).get! - (st.felts y.name).get!
  | Mul x y       => .Val <| (st.felts x.name).get! * (st.felts y.name).get!
  | Pow x y       => .Val <| (st.felts x.name).get! ^ y
  | Neg x         => .Val <| 0 - (st.felts x.name).get!
  | AndEqz c x    => .Constraint <| (st.props c.name).get! ∧ (st.felts x.name).get! = 0
  | AndCond old cond inner =>
      .Constraint <| (st.props old.name).get! ∧
                     if (st.felts cond.name).get! = 0
                       then _root_.True
                       else (st.props inner.name).get!
  | Isz x         => .Val $ if (st.felts x.name).get! = 0 then 1 else 0
  | Inv x         => .Val $ match st.felts x.name with
                              | some x => if x = 0 then 0 else x⁻¹
                              | _      => default

notation:61 "Γ " st:max " ⟦" p:49 "⟧ₑ" => Op.eval st p

namespace MLIRNotation

end MLIRNotation

namespace Op

section Op

open MLIRNotation

variable {st : State} {α : IsNondet}

@[simp]
lemma eval_const : Γ st ⟦@Const α x⟧ₑ = .Val x := rfl

@[simp]
lemma eval_true : Γ st ⟦@Op.True α⟧ₑ = .Constraint (_root_.True) := rfl

@[simp]
lemma eval_getInput : Γ st ⟦@GetInput α i x⟧ₑ = .Val (st.input.get! i) := rfl

@[simp]
lemma eval_getOutput : Γ st ⟦@GetOutput α i x⟧ₑ = .Val (st.output.get! i) := rfl

@[simp]
lemma eval_sub : Γ st ⟦@Sub α x y⟧ₑ = .Val ((st.felts x.name).get! - (st.felts y.name).get!) := rfl

@[simp]
lemma eval_mul : Γ st ⟦@Mul α x y⟧ₑ = .Val ((st.felts x.name).get! * (st.felts y.name).get!) := rfl

@[simp]
lemma eval_isz : Γ st ⟦??₀x⟧ₑ = .Val (if (st.felts x.name).get! = 0 then 1 else 0) := rfl

@[simp]
lemma eval_inv : Γ st ⟦Inv x⟧ₑ = .Val (match st.felts x.name with
                                        | some x => if x = 0 then 0 else x⁻¹
                                        | _      => default) := rfl

@[simp]
lemma eval_andEqz : Γ st ⟦@AndEqz α c x⟧ₑ =
                    .Constraint ((st.props c.name).get! ∧ (st.felts x.name).get! = 0) := rfl

@[simp]
lemma eval_andCond :
  Γ st ⟦@AndCond α old cnd inner⟧ₑ =
    .Constraint ((st.props old.name).get! ∧
                 if (st.felts cnd.name).get! = 0
                   then _root_.True
                   else (st.props inner.name).get!) := rfl

end Op

end Op

inductive MLIR : IsNondet → Type where
  | Assign : String → Op x → MLIR x
  | Eqz : Variable FeltTag → MLIR x
  | If : Variable FeltTag → MLIR x → MLIR x
  | Nondet : MLIR InNondet → MLIR NotInNondet
  | Sequence : MLIR x → MLIR x → MLIR x
  | SetOutput : ℕ → Variable FeltTag → MLIR InNondet

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

abbrev withEqZero (x : Felt) (st : State) : State :=
  {st with constraints := (x = 0) :: st.constraints}

@[simp]
lemma withEqZero_def : withEqZero x st = {st with constraints := (x = 0) :: st.constraints} := rfl

-- Step through the entirety of a `MLIR` MLIR program from initial state
-- `state`, yielding the post-execution state and possibly a constraint
-- (`Prop`), the return value of the program.
def MLIR.run {α : IsNondet} (program : MLIR α) (st : State) : State :=
  match program with
    | Assign name op => st[name] := Γ st ⟦op⟧ₑ
    | Eqz x =>
        match st.felts x.name with
          | .some x => withEqZero x st
          | _       => st
    | If x program =>
        match st.felts x.name with
          | some x => if x = 0 then st else program.run st
          | _      => st
    | Nondet block => block.run st
    | Sequence a b => b.run (a.run st)
    | SetOutput i x =>
        match st.felts x.name with
          | .some x => {st with output := st.output.set i x}
          | _       => st

@[simp]
abbrev MLIR.runProgram (program : MLIRProgram) := program.run

notation:61 "Γ " st:max " ⟦" p:49 "⟧" => MLIR.run p st

end Risc0
