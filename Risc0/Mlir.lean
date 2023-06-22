import Risc0.Basic
import Risc0.Buffer
import Risc0.State

namespace Risc0

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
  | Add : FeltVar → FeltVar → Op x
  | Sub : FeltVar → FeltVar → Op x
  | Neg : FeltVar           → Op x
  | Mul : FeltVar → FeltVar → Op x
  | Pow : FeltVar → ℕ       → Op x
  | Inv : FeltVar           → Op InNondet
  -- Logic
  | Isz : FeltVar → Op InNondet
  -- Constraints
  | AndEqz  : PropVar → FeltVar           → Op x
  | AndCond : PropVar → FeltVar → PropVar → Op x
  -- Buffers
  | Alloc     : ℕ                    → Op x
  | Back      : BufferVar → ℕ        → Op x
  | Get       : BufferVar → Back → ℕ → Op x
  | GetGlobal : BufferVar → ℕ        → Op x
  | Slice     : BufferVar → ℕ    → ℕ → Op x

open Op VarType

instance : HAdd (FeltVar) (FeltVar) (Op IsNondet.InNondet)    := ⟨Op.Add⟩
instance : HAdd (FeltVar) (FeltVar) (Op IsNondet.NotInNondet) := ⟨Op.Add⟩

instance : HSub (FeltVar) (FeltVar) (Op IsNondet.InNondet)    := ⟨Op.Sub⟩
instance : HSub (FeltVar) (FeltVar) (Op IsNondet.NotInNondet) := ⟨Op.Sub⟩

instance : HMul (FeltVar) (FeltVar) (Op IsNondet.InNondet)    := ⟨Op.Mul⟩
instance : HMul (FeltVar) (FeltVar) (Op IsNondet.NotInNondet) := ⟨Op.Mul⟩

instance : HPow (FeltVar) ℕ (Op IsNondet.InNondet)    := ⟨Op.Pow⟩
instance : HPow (FeltVar) ℕ (Op IsNondet.NotInNondet) := ⟨Op.Pow⟩

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

def isGetValid (st : State) (buf : BufferVar) (back : Back) (offset : ℕ) :=
  back ≤ st.cycle ∧
  buf ∈ st.vars ∧
  offset < st.bufferWidths[buf].get! ∧
  (st.get_back buf back offset).isSome

lemma isGetValid_def :
  isGetValid st buf back offset = 
  (back ≤ st.cycle ∧
   buf ∈ st.vars ∧
   offset < st.bufferWidths[buf].get! ∧
   (st.get_back buf back offset).isSome) := rfl

instance : Decidable (isGetValid st buf back offset) := by unfold isGetValid; exact inferInstance

def getImpl (st : State) (buf : BufferVar) (back : Back) (offset : ℕ) :=
  if isGetValid st buf back offset
  then Option.some <| Lit.Val (st.get_back buf back offset).get!
  else .none

lemma getImpl_def : getImpl st buf back offset = 
                    if isGetValid st buf back offset
                    then Option.some <| Lit.Val (st.get_back buf back offset).get!
                    else .none := rfl

-- Evaluate a pure functional circuit.
def Op.eval {x} (st : State) (op : Op x) : Option Lit :=
  match op with
    -- Constants
    | Const const => .some <| .Val const
    -- Arith
    | Add lhs rhs => .some <| .Val <| st.felts[lhs].get! + st.felts[rhs].get!
    | Sub lhs rhs => .some <| .Val <| st.felts[lhs].get! - st.felts[rhs].get!
    | Neg lhs     => .some <| .Val <| 0                  - st.felts[lhs].get!
    | Mul lhs rhs => .some <| .Val <| st.felts[lhs].get! * st.felts[rhs].get!
    | Pow lhs rhs => .some <| .Val <| st.felts[lhs].get! ^ rhs
    | Inv x => .some <| .Val <| if st.felts[x]!.get! = 0 then 0 else st.felts[x]!.get!⁻¹
    -- Logic
    | Isz x => .some <| .Val <| if st.felts[x]!.get! = 0 then 1 else 0
    -- Constraints
    | AndEqz c val           => .some <| .Constraint <| st.props[c].get! ∧ st.felts[val].get! = 0
    | AndCond old cond inner =>
        .some <| .Constraint <| st.props[old].get! ∧
                                if st.felts[cond].get! = 0
                                then _root_.True
                                else st.props[inner].get!
    | True                   => .some <| .Constraint _root_.True
    -- Buffers
    | Alloc size           => .some <| .Buf <| List.replicate size .none
    | Back buf back        => .some <| .Buf <| st.buffers[buf].get![st.cycle]!.slice 0 back
    | Get buf back offset  => getImpl st buf back offset
    | GetGlobal buf offset => if buf ∈ st.vars
                              then
                                let buffer := st.buffers[buf].get!
                                let bufferWidth := st.bufferWidths[buf].get!
                                let idx := Buffer.Idx.from1D offset bufferWidth -- the implementation of getGlobal steps directly into the 1D representation of whatever buffer it is passed
                                let val := buffer.get! idx
                                if idx.time < buffer.length ∧ val.isSome
                                then .some <| .Val val.get!
                                else .none
                              else .none
    | Slice buf offset size => .some <| .Buf <| (List.get! (st.buffers buf).get! (st.cycle - 1)).slice offset size

namespace MLIRNotation

notation:61 "Γ " st:max " ⟦" p:49 "⟧ₑ" => Op.eval st p

end MLIRNotation

namespace Op

open MLIRNotation

variable {st : State} {α : IsNondet}

@[simp]
lemma eval_const : Γ st ⟦@Const α x⟧ₑ = .some (.Val x) := rfl

@[simp]
lemma eval_true : Γ st ⟦@Op.True α⟧ₑ = .some (.Constraint (_root_.True)) := rfl

@[simp]
lemma eval_getBuffer : Γ st ⟦@Get α buf back offset⟧ₑ =
  let val := (st.buffers[buf].get!).get! ((st.cycle - back.toNat), offset)
  if back ≤ st.cycle ∧ buf ∈ st.vars ∧ offset < st.bufferWidths[buf].get! ∧ val.isSome
  then .some (.Val val.get!)
  else .none := rfl

@[simp]
lemma eval_add : Γ st ⟦@Add α x y⟧ₑ = .some (.Val (st.felts[x].get! + st.felts[y].get!)) := rfl

@[simp]
lemma eval_sub : Γ st ⟦@Sub α x y⟧ₑ = .some (.Val (st.felts[x].get! - st.felts[y].get!)) := rfl

@[simp]
lemma eval_mul : Γ st ⟦@Mul α x y⟧ₑ = .some (.Val (st.felts[x].get! * st.felts[y].get!)) := rfl

@[simp]
lemma eval_isz : Γ st ⟦??₀x⟧ₑ = .some (.Val (if st.felts[x].get! = 0 then 1 else 0)) := rfl

@[simp]
lemma eval_inv : Γ st ⟦Inv x⟧ₑ = .some (.Val (if st.felts[x]!.get! = 0 then 0 else st.felts[x]!.get!⁻¹)) := rfl

@[simp]
lemma eval_andEqz : Γ st ⟦@AndEqz α c x⟧ₑ =
                    .some (.Constraint (st.props[c].get! ∧ st.felts[x].get! = 0)) := rfl

@[simp]
lemma eval_andCond :
  Γ st ⟦@AndCond α old cnd inner⟧ₑ =
    .some (.Constraint (st.props[old].get! ∧
                       if st.felts[cnd].get! = 0
                       then _root_.True
                       else st.props[inner].get!)) := rfl

end Op

inductive MLIR : IsNondet → Type where
  -- Meta
  | Assign    : String        → Op x   → MLIR x
  | Eqz       : FeltVar                → MLIR x
  | If        : FeltVar       → MLIR x → MLIR x
  | Nondet    : MLIR InNondet          → MLIR NotInNondet
  | Sequence  : MLIR x        → MLIR x → MLIR x
  -- Ops
  | Fail      :                           MLIR x
  | Set       : BufferVar → ℕ → FeltVar → MLIR InNondet
  | SetGlobal : BufferVar → ℕ → FeltVar → MLIR InNondet

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

-- Step through the entirety of a `MLIR` MLIR program from initial state
-- `state`, yielding the post-execution state and possibly a constraint
-- (`Prop`), the return value of the program.
def MLIR.run {α : IsNondet} (program : MLIR α) (st : State) : State :=
  match program with
    -- Meta
    | Assign name op => st[name] ←ₛ Γ st ⟦op⟧ₑ
    | Eqz x          => st.withEqZero st.felts[x]!.get!
    | If x program   => if st.felts[x]!.get! = 0 then st else program.run st
    | Nondet block   => block.run st
    | Sequence a b   => b.run (a.run st)
    -- Ops
    | Fail                     => {st with isFailed := true}
    | Set buf offset val       => st.set! buf offset st.felts[val]!.get!
    | SetGlobal buf offset val => st.setGlobal! buf offset st.felts[val]!.get! -- Behind the scenes setGlobal actually flattens a 2d buffer into a 1d buffer
                                                                               -- and indexes into it. This is a side effect of global buffers only being 1d anyway

@[simp]
abbrev MLIR.runProgram (program : MLIRProgram) := program.run

namespace MLIRNotation

notation:61 "Γ " st:max " ⟦" p:49 "⟧" => MLIR.run p st

end MLIRNotation

end Risc0
