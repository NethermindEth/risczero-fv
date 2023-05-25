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

inductive VarType := | FeltTag | PropTag | BufferTag deriving DecidableEq

open VarType

structure Variable (tag : VarType) :=
  name : String
deriving DecidableEq

-- Imagine using dependent types.
abbrev Buffer (α : Type) (n : ℕ) := List (Vector α n)

def Buffer.empty {α : Type} (n : ℕ) : Buffer α n := []

-- A finite field element.
abbrev Felt := ZMod P

-- A literal, either a finite field element, a constraint or a buffer.
inductive Lit where
  | Buf        : Buffer Felt n → Lit
  | Constraint : Prop          → Lit
  | Val        : Felt          → Lit

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

def Back := ℕ

@[simp]
def Back.toNat (back : Back) : ℕ := back

instance : HSub ℕ Back Back := ⟨λ lhs rhs => lhs - rhs.toNat⟩
instance : OfNat Back n := ⟨n⟩

instance {α : Type} {n : ℕ} : GetElem (Buffer α n) (Back × Fin n) α λ buf i =>
                                i.1.toNat < buf.length :=
  ⟨λ buf i h => buf[i.1.toNat]'h |>.get i.2⟩

instance {α : Type} {n : ℕ} : GetElem (Buffer α n) (Back × ℕ) α λ buf i =>
                                i.1.toNat < buf.length ∧ i.2 < n :=
  ⟨λ buf i h => buf[(i.1, @Fin.mk n i.2 h.2)]'h.1⟩

def Buffer.set (buf : Buffer Felt n) (cycle : ℕ) (offset : Fin n) (val : Felt) : Buffer Felt n :=
  List.set buf cycle (buf[cycle]!.set offset val)

-- Imagine using dependent types... don't ever git blame this.
-- Maybe we can use (Variable <Tag>) as keys here, it's somewhat annoying tho.
structure State where
  felts       : Map String Felt
  props       : Map String Prop
  buffers     : Map String (Σ n : ℕ, Buffer Felt n)
  constraints : List Prop
  cycle       : ℕ

def State.update (state : State) (name : String) (x : Lit) : State :=
  match x with
    | @Lit.Buf n b  => {state with buffers := state.buffers[name] := ⟨n, b⟩}
    | .Constraint c => {state with props := state.props[name] := c}
    | .Val x        => {state with felts := state.felts[name] := x}

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

-- @[simp]
-- lemma State.if_output {state₁ state₂ : State} {x : Felt} :
--   (if x = 0 then state₁ else state₂).output =
--   if (x = 0) then state₁.output else state₂.output := by apply apply_ite

notation:61 st "[" n:61 "]" " := " x:49 => State.update st n x

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
  -- Constants
  | Const : Felt → Op x
  | True  : Op x
  -- Arith
  | Add : Variable FeltTag → Variable FeltTag → Op x
  | Sub : Variable FeltTag → Variable FeltTag → Op x
  | Neg : Variable FeltTag                    → Op x
  | Mul : Variable FeltTag → Variable FeltTag → Op x
  | Pow : Variable FeltTag → ℕ                → Op x
  | Inv : Variable FeltTag                    → Op InNondet
  -- Logic
  | Isz : Variable FeltTag → Op InNondet
  -- Constraints
  | AndEqz  : Variable PropTag → Variable FeltTag                    → Op x
  | AndCond : Variable PropTag → Variable FeltTag → Variable PropTag → Op x
  -- Buffers
  | Alloc : ℕ                                 → Op x
  | Back  : Variable BufferTag → ℤ        → Op x
  | Get   : Variable BufferTag → Back → ℕ → Op x
  | Slice : Variable BufferTag → ℕ    → ℕ → Op x

open Op VarType

instance : HAdd (Variable FeltTag) (Variable FeltTag) (Op IsNondet.InNondet)    := ⟨Op.Add⟩
instance : HAdd (Variable FeltTag) (Variable FeltTag) (Op IsNondet.NotInNondet) := ⟨Op.Add⟩

instance : HSub (Variable FeltTag) (Variable FeltTag) (Op IsNondet.InNondet)    := ⟨Op.Sub⟩
instance : HSub (Variable FeltTag) (Variable FeltTag) (Op IsNondet.NotInNondet) := ⟨Op.Sub⟩

instance : HMul (Variable FeltTag) (Variable FeltTag) (Op IsNondet.InNondet)    := ⟨Op.Mul⟩
instance : HMul (Variable FeltTag) (Variable FeltTag) (Op IsNondet.NotInNondet) := ⟨Op.Mul⟩

instance : HPow (Variable FeltTag) ℕ (Op IsNondet.InNondet)    := ⟨Op.Pow⟩
instance : HPow (Variable FeltTag) ℕ (Op IsNondet.NotInNondet) := ⟨Op.Pow⟩

-- Notation for Ops.
namespace MLIRNotation

scoped prefix  :max                    "C"                               => Op.Const
scoped notation:max                    "⊤"                               => Op.True
scoped notation:max (priority := high) b "[" "(" r ", " n ")" "]"        => Op.Get b n r
scoped infix   :55                     " &₀ "                            => Op.AndEqz
scoped notation:55                     " guard " c " & " x " with " y:55 => Op.AndCond x c y
scoped prefix  :57                     "??₀"                             => Op.Isz
scoped prefix  :max                    "Inv"                             => Op.Inv

end MLIRNotation

instance : Inhabited Felt := ⟨-42⟩

def State.get! (st : State) (buf : Variable BufferTag) (back : Back) (offset : ℕ) : Felt := 
  (st.buffers buf.name).get!.2[(st.cycle - back, offset)]!

def Buffer.slice (buf : Buffer α n) (offset size : ℕ) : Buffer α n :=
  buf.drop offset |>.take size

-- Evaluate a pure functional circuit.
def Op.eval {x} (st : State) (op : Op x) : Lit :=
  match op with
    -- Constants
    | Const const => .Val const
    | True        => .Constraint _root_.True
    -- Arith
    | Add lhs rhs => .Val <| (st.felts lhs.name).get! + (st.felts rhs.name).get!
    | Sub lhs rhs => .Val <| (st.felts lhs.name).get! - (st.felts rhs.name).get!
    | Neg lhs     => .Val <| 0                        - (st.felts lhs.name).get!
    | Mul lhs rhs => .Val <| (st.felts lhs.name).get! * (st.felts rhs.name).get!
    | Pow lhs rhs => .Val <| (st.felts lhs.name).get! ^ rhs
    | Inv x => .Val <| match st.felts x.name with
                         | some x => if x = 0 then 0 else x⁻¹
                         | _      => default
    -- Logic
    | Isz x => .Val <| if (st.felts x.name).get! = 0 then 1 else 0
    -- Constraints
    | AndEqz c val           => .Constraint <| (st.props c.name).get! ∧ (st.felts val.name).get! = 0
    | AndCond old cond inner =>
        .Constraint <| (st.props old.name).get! ∧
                       if (st.felts cond.name).get! = 0
                         then _root_.True
                         else (st.props inner.name).get!
    -- Buffers
    | Alloc size            => .Buf <| Buffer.empty size
    | Back buf back         => .Buf <| (st.buffers buf.name).get!.2.slice 0 back.toNat -- Why is back signed; this toNat is wrong here, naturally.
    | Get buf back offset   => .Val <| st.get! buf back offset
    | Slice buf offset size => .Buf <| (st.buffers buf.name).get!.2.slice offset size

notation:61 "Γ " st:max " ⟦" p:49 "⟧ₑ" => Op.eval st p

namespace MLIRNotation

end MLIRNotation

namespace Op

-- TODO(move this out)

section Op

open MLIRNotation

variable {st : State} {α : IsNondet}

@[simp]
lemma eval_const : Γ st ⟦@Const α x⟧ₑ = .Val x := rfl

@[simp]
lemma eval_true : Γ st ⟦@Op.True α⟧ₑ = .Constraint (_root_.True) := rfl

@[simp]
lemma eval_getBuffer : Γ st ⟦@Get α buf back offset⟧ₑ =
  .Val (st.buffers buf.name).get!.2[(st.cycle - back, offset)]! := rfl

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
  -- Meta
  | Assign    : String           → Op x   → MLIR x
  | Eqz       : Variable FeltTag          → MLIR x
  | If        : Variable FeltTag → MLIR x → MLIR x
  | Nondet    : MLIR InNondet             → MLIR NotInNondet
  | Sequence  : MLIR x           → MLIR x → MLIR x
  -- Ops
  | Set   : Variable BufferTag → ℕ → Variable FeltTag → MLIR InNondet

-- Notation for MLIR programs.  
namespace MLIRNotation

scoped infix   :51                    "←ₐ "                      => MLIR.Assign
scoped prefix  :52                    "?₀"                       => MLIR.Eqz
scoped notation:51                    "guard " c " then " x:51   => MLIR.If c x
scoped prefix  :max                   "nondet"                   => MLIR.Nondet
scoped infixr  :50                    "; "                       => MLIR.Sequence
scoped notation:51 (priority := high) b "[" v:51 "]" " ←ᵢ " x:51 => MLIR.Set b v x

end MLIRNotation

abbrev MLIRProgram := MLIR NotInNondet

abbrev withEqZero (x : Felt) (st : State) : State :=
  {st with constraints := (x = 0) :: st.constraints}

@[simp]
lemma withEqZero_def : withEqZero x st = {st with constraints := (x = 0) :: st.constraints} := rfl

def State.set! (st : State) (buffer : Variable BufferTag) (offset : ℕ) (val : Felt) : State := 
  let ⟨sz, data⟩ := st.buffers buffer.name |>.get!
  if h : sz ≤ offset
    then st
    else {st with buffers := st.buffers[buffer.name] :=
                               ⟨sz, data.set st.cycle ⟨offset, Nat.lt_of_not_le h⟩ val⟩}

-- Step through the entirety of a `MLIR` MLIR program from initial state
-- `state`, yielding the post-execution state and possibly a constraint
-- (`Prop`), the return value of the program.
def MLIR.run {α : IsNondet} (program : MLIR α) (st : State) : State :=
  match program with
    -- Meta
    | Assign name op => st[name] := Γ st ⟦op⟧ₑ
    | Eqz x =>
        match st.felts x.name with
          | .some x => withEqZero x st
          | _       => st
    | If x program =>
        match st.felts x.name with
          | .some x => if x = 0 then st else program.run st
          | _       => st
    | Nondet block => block.run st
    | Sequence a b => b.run (a.run st)
    -- Ops
    | Set buf offset val =>
        match st.felts val.name with
          | .some val => st.set! buf offset val
          | _         => st

@[simp]
abbrev MLIR.runProgram (program : MLIRProgram) := program.run

notation:61 "Γ " st:max " ⟦" p:49 "⟧" => MLIR.run p st

end Risc0
