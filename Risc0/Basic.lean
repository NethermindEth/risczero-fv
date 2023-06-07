import Mathlib.Data.Nat.Prime
import Mathlib.Data.Finmap
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Risc0.Map
import Risc0.Wheels

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

abbrev BufferVar := Variable BufferTag
abbrev FeltVar := Variable FeltTag
abbrev PropVar := Variable PropTag

abbrev Felt := ZMod P

-- none is an unset value which can be written to, but not read
-- some is a set value which can be read, and can only be written to if the new val is equal
abbrev BufferAtTime := List (Option Felt)

abbrev Buffer := List BufferAtTime

namespace Buffer

def empty : Buffer := []

def set! (row : BufferAtTime) (buf : Buffer) : Buffer :=
  List.set buf (buf.length - 1) row

lemma set!_of_nonempty {buf : Buffer} (h : buf ≠ []) : buf.set! row ≠ [] := by
  unfold set!; aesop

def init (size : ℕ) : Buffer := [List.replicate size .none]

def init' (row : BufferAtTime) : Buffer := [row]

def last! (buf : Buffer) : BufferAtTime :=
  buf.getLast!

def copyLast (buf : Buffer) : Buffer := 
  buf.push buf.last!

def setLatestUnchecked (buf : Buffer) (val : BufferAtTime) : Buffer :=
  List.set buf (buf.length - 1) val

def setAtTimeChecked (buf : Buffer) (timeIdx: ℕ) (dataIdx: ℕ) (val: Felt) : Option Buffer :=
  let bufferAtTime := buf.get! timeIdx
  let oldVal := (bufferAtTime.get! dataIdx)
  if oldVal.isEqSome val
  then .some buf
  else
    if oldVal.isNone
    then .some <| List.set buf timeIdx (bufferAtTime.set dataIdx (.some val))
    else .none

def isValidUpdate (old new : BufferAtTime) :=
  old.length = new.length ∧
  (List.zip old new).all
    λ pair => pair.fst.isNone ∨ pair.fst = pair.snd

end Buffer

inductive Lit where
  | Buf        : BufferAtTime → Lit
  | Constraint : Prop         → Lit
  | Val        : Felt         → Lit

structure State where
  -- Context of buffers.
  buffers      : Map BufferVar Buffer
  -- A widths for every buffer.
  bufferWidths : Map BufferVar ℕ
  -- Intermediate constraints.
  constraints  : List Prop
  -- Current cycle.
  cycle        : ℕ
  -- Temporary felts.
  felts        : Map FeltVar Felt
  -- Is the state invalid.
  isFailed     : Bool
  -- Context of propositions.
  props        : Map PropVar Prop
  -- Valid variables for buffers.
  vars         : List BufferVar

abbrev Input := "input"
abbrev Output := "output"

namespace State

section State

variable (st : State)

def varsConsistent := ∀ var, var ∈ st.vars ↔ var ∈ st.buffers

def cycleIsRows := ∀ var (h₁ : var ∈ st.buffers), (st.buffers.get h₁).length = st.cycle + 1

def colsConsistent := ∀ var, var ∈ st.vars ↔ var ∈ st.bufferWidths

def bufferLensConsistent :=
  ∀ var (h : var ∈ st.buffers) (h₁ : cycleIsRows st),
    ∀ row (h₂ : row ≤ st.cycle),
      have : row < (st.buffers.get h).length := by rw [h₁]; linarith
      st.bufferWidths var = (st.buffers.get h)[row].length

structure WellFormed (st : State) : Prop := 
  -- Variable-names/keys of the buffers map are distinct.
  distinct : st.vars.Nodup
  -- Variable-names describe valid buffers.
  hVars    : varsConsistent st
  -- There are as many rows in each valid buffer as there are cycles (+1)
  hCycle   : cycleIsRows st
  -- Variable-names describe valid rows.
  hCols    : colsConsistent st
  -- Every valid row has a known length stored in cols.
  hColsLen : bufferLensConsistent st
  
def Valid (st : State) := st.WellFormed ∧ st.isFailed

def init (numInput numOutput : ℕ)
          (input : BufferAtTime) (output : BufferAtTime)
          (_hIn : input.length = numInput) (_hOut : output.length = numOutput) : State where
  buffers      := Map.fromList [(⟨Input⟩, Buffer.init' input), (⟨Output⟩, Buffer.init' output)]
  bufferWidths := Map.fromList [(⟨Input⟩, numInput), (⟨Output⟩, numOutput)]
  constraints  := []
  cycle        := 0
  felts        := Map.empty
  isFailed     := false
  props        := Map.empty
  vars         := [⟨Input⟩, ⟨Output⟩]

-- Shouldn't be necessary, because why would we want state to have default initialised input
def init_default (numInput numOutput : ℕ) : State :=
  init numInput numOutput
        ((Buffer.init numInput).head (by simp [Buffer.init]))
        ((Buffer.init numOutput).head (by simp [Buffer.init]))
        (by simp [Buffer.init])
        (by simp [Buffer.init])

private lemma valid_init'_aux :
  bufferLensConsistent (State.init m n input output hIn hOut) := λ var h h₁ row h₂ => by
  simp [bufferWidths, init, Buffer.init']
  have : var = ⟨Input⟩ ∨ var = ⟨Output⟩ := by
    unfold init at h; rw [Map.mem_fromList] at h; simp at h; exact h
  have : row = 0 := by simp [init] at h₂; exact h₂
  subst this; simp
  rcases this with h | h <;> subst h <;> simp [Map.update, Map.getElem_def, *]

lemma valid_init' : (init m n input output hIn hOut).WellFormed where
  distinct := by simp [init]
  hVars    := λ var => ⟨
      λ h => by simp [init] at *; rcases h with h | h <;> subst h ; decide_mem_map,
      λ h => by simp [init] at *; simp [Map.mem_def, Map.update] at h; split at h <;> aesop 
    ⟩ 
  hCycle   := λ var h =>
    by have : var = ⟨Input⟩ ∨ var = ⟨Output⟩ := by
         simp only [init] at h; rw [Map.mem_fromList] at h; simp at h; exact h
       rcases this with h | h <;> subst h <;> simp [Map.getElem_def] <;> rfl
  hCols    := λ var => ⟨
      λ h => by simp [init] at h; rcases h with h | h <;> subst h ; decide_mem_map,
      λ h => by simp [init] at h ⊢; simp [Map.mem_def, Map.update] at h; aesop
    ⟩ 
  hColsLen := valid_init'_aux

lemma valid_init : (init_default m n).WellFormed := valid_init'

def update (state : State) (name : String) (x : Option Lit) : State :=
  match x with
    | .none => {state with isFailed := true}
    | .some lit =>
      match lit with
        | .Constraint c => {state with props := state.props[⟨name⟩] := c}
        | .Val        x => {state with felts := state.felts[⟨name⟩] := x}
        | @Lit.Buf    newBufferAtTime =>
          match (state.buffers ⟨name⟩) with
            | .some oldBuffer =>
              if
                oldBuffer.last!.length ≠ newBufferAtTime.length ∨
                (List.zip oldBuffer.last! newBufferAtTime).any
                  λ pair => pair.fst.isSome ∧ pair.snd.isSome ∧ pair.fst.get! ≠ pair.snd.get!
              then {state with isFailed := true}
              else {state with buffers := state.buffers[⟨name⟩] := (oldBuffer.setLatestUnchecked newBufferAtTime)}
            | .none        => {state with isFailed := true}

@[simp]
lemma update_val {state : State} {name : String} {x : Felt} :
  update state name (.some (.Val x)) = { state with felts := state.felts.update ⟨name⟩ x } := rfl

@[simp]
lemma update_constraint {state : State} {name : String} {c : Prop} :
  update state name (.some (.Constraint c)) = { state with props := state.props.update ⟨name⟩ c } := rfl

@[simp]
lemma if_constraints {state₁ state₂ : State} {x : Felt} :
  (if x = 0 then state₁ else state₂).constraints =
  if x = 0 then state₁.constraints else state₂.constraints := by apply apply_ite

end State

end State

instance : Inhabited State := ⟨State.init_default 42 42⟩

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

def Back := ℕ 

def Back.toNat (n : Back) : ℕ := n

instance : LinearOrderedCommSemiring Back := by unfold Back; exact inferInstance

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

instance : Inhabited Felt := ⟨-42⟩

def BufferAtTime.slice (buf : BufferAtTime) (offset size : ℕ) : BufferAtTime :=
  buf.drop offset |>.take size

def rowColOfWidthIdx (width idx : ℕ) : Back × ℕ := (idx / width, idx % width)

lemma col_lt_width (h : 0 < width) : (rowColOfWidthIdx width idx).2 < width := Nat.mod_lt _ h

-- Evaluate a pure functional circuit.
def Op.eval {x} (st : State) (op : Op x) : Option Lit :=
  match op with
    -- Constants
    | Const const => .some <| .Val const
    | True        => .some <| .Constraint _root_.True
    -- Arith
    | Add lhs rhs => .some <| .Val <| (st.felts lhs).get! + (st.felts rhs).get!
    | Sub lhs rhs => .some <| .Val <| (st.felts lhs).get! - (st.felts rhs).get!
    | Neg lhs     => .some <| .Val <| 0                   - (st.felts lhs).get!
    | Mul lhs rhs => .some <| .Val <| (st.felts lhs).get! * (st.felts rhs).get!
    | Pow lhs rhs => .some <| .Val <| (st.felts lhs).get! ^ rhs
    | Inv x => .some <| .Val <|
                 match st.felts x with
                   | some x => if x = 0 then 0 else x⁻¹
                   | _      => default
    -- Logic
    | Isz x => .some <| .Val <| if (st.felts x).get! = 0 then 1 else 0
    -- Constraints
    | AndEqz c val           => .some <| .Constraint <| (st.props c).get! ∧ (st.felts val).get! = 0
    | AndCond old cond inner =>
        .some <| .Constraint <|
          (st.props old).get! ∧
            if (st.felts cond).get! = 0
            then _root_.True
            else (st.props inner).get!
    -- Buffers
    | Alloc size          => .some <| .Buf <| List.replicate size .none
    | Back buf back       => .some <| .Buf <| (List.get! (st.buffers.get! buf) st.cycle).slice 0 back
    | Get buf back offset => let val := ((st.buffers.get! buf).get! (st.cycle - back.toNat)).get! offset
                              if
                                back ≤ st.cycle ∧
                                buf ∈ st.vars ∧
                                offset < st.bufferWidths.get! buf ∧
                                val.isSome
                              then .some <| .Val <| val.get!
                              else .none
    | GetGlobal buf offset => if buf ∈ st.vars
                              then
                                let buffer := (st.buffers.get! buf)
                                let bufferWidth := st.bufferWidths.get! buf
                                let timeIdx := offset.div bufferWidth -- the implementation of getGlobal steps directly into the 1D representation
                                let dataIdx := offset.mod bufferWidth -- of whatever buffer it is passed
                                let val := (buffer.get! timeIdx).get! dataIdx
                                if timeIdx < buffer.length ∧ dataIdx < bufferWidth ∧ val.isSome
                                then .some <| .Val <| val.get!
                                else .none
                              else .none
    | Slice buf offset size => .some <| .Buf <| (List.get! (st.buffers buf).get! (st.cycle - 1)).slice offset size

notation:61 "Γ " st:max " ⟦" p:49 "⟧ₑ" => Op.eval st p

namespace MLIRNotation

end MLIRNotation

namespace Op

-- TODO(move this out)

section Op

open MLIRNotation

variable {st : State} {α : IsNondet}

@[simp]
lemma eval_const : Γ st ⟦@Const α x⟧ₑ = .some (.Val x) := rfl

@[simp]
lemma eval_true : Γ st ⟦@Op.True α⟧ₑ = .some (.Constraint (_root_.True)) := rfl

@[simp]
lemma eval_getBuffer : Γ st ⟦@Get α buf back offset⟧ₑ =
  let val := ((st.buffers buf).get!.get! (st.cycle - (back.toNat)) |>.get! offset)
  if back ≤ st.cycle ∧ buf ∈ st.vars ∧ offset < st.bufferWidths.get! buf ∧ val.isSome
  then .some (.Val val.get!)
  else .none := rfl

@[simp]
lemma eval_sub : Γ st ⟦@Sub α x y⟧ₑ = .some (.Val ((st.felts x).get! - (st.felts y).get!)) := rfl

@[simp]
lemma eval_mul : Γ st ⟦@Mul α x y⟧ₑ = .some (.Val ((st.felts x).get! * (st.felts y).get!)) := rfl

@[simp]
lemma eval_isz : Γ st ⟦??₀x⟧ₑ = .some (.Val (if (st.felts x).get! = 0 then 1 else 0)) := rfl

@[simp]
lemma eval_inv : Γ st ⟦Inv x⟧ₑ = .some (.Val (match st.felts x with
                                               | some x => if x = 0 then 0 else x⁻¹
                                               | _      => default)) := rfl

@[simp]
lemma eval_andEqz : Γ st ⟦@AndEqz α c x⟧ₑ =
                    .some (.Constraint ((st.props c).get! ∧ (st.felts x).get! = 0)) := rfl

@[simp]
lemma eval_andCond :
  Γ st ⟦@AndCond α old cnd inner⟧ₑ =
    .some (.Constraint ((st.props old).get! ∧
                       if (st.felts cnd).get! = 0
                       then _root_.True
                       else (st.props inner).get!)) := rfl

end Op

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

abbrev withEqZero (x : Felt) (st : State) : State :=
  {st with constraints := (x = 0) :: st.constraints}

@[simp]
lemma withEqZero_def : withEqZero x st = {st with constraints := (x = 0) :: st.constraints} := rfl

def State.setBufferElementImpl (st : State) (bufferVar : BufferVar) (timeIdx dataIdx: ℕ) (val : Felt) : State :=
  match (st.buffers.get! bufferVar).setAtTimeChecked timeIdx dataIdx val with
    | .some b => {st with buffers := st.buffers[bufferVar] := b}
    | .none   => {st with isFailed := true}

def State.set! (st : State) (bufferVar : BufferVar) (offset : ℕ) (val : Felt) : State :=
  st.setBufferElementImpl bufferVar ((st.buffers.get! bufferVar).length - 1) offset val

def State.setGlobal! (st : State) (bufferVar : BufferVar) (offset : ℕ) (val : Felt) : State :=
  let width := st.bufferWidths.get! bufferVar
  st.setBufferElementImpl bufferVar (offset.div width) (offset.mod width) val

private lemma State.setGlobal!aux {P : Prop} (h : ¬(P ∨ sz = 0)) : 0 < sz := by
  rw [not_or] at h; rcases h with ⟨_, h⟩
  exact Nat.zero_lt_of_ne_zero h

-- def State.setGlobal! (st : State) (buffer : BufferVar) (idx : ℕ) (val : Felt) : State := sorry 
  -- let ⟨sz, data⟩ := st.buffers buffer |>.get!
  -- let rowCol := rowColOfWidthIdx sz idx
  -- if h : rowCol.1 ≠ st.cycle ∨ sz = 0
  --   then st
  --   else {st with buffers :=
  --           st.buffers[buffer.name] :=
  --             ⟨sz, data.set rowCol.1 ⟨rowCol.2, col_lt_width (State.setGlobal!aux h)⟩ val⟩}

-- Step through the entirety of a `MLIR` MLIR program from initial state
-- `state`, yielding the post-execution state and possibly a constraint
-- (`Prop`), the return value of the program.
def MLIR.run {α : IsNondet} (program : MLIR α) (st : State) : State :=
  match program with
    -- Meta
    | Assign name op => st[name] := Γ st ⟦op⟧ₑ
    | Eqz x =>
        match st.felts x with
          | .some x => withEqZero x st
          | _       => st
    | If x program => 
        match st.felts x with
          | .some x => if x = 0 then st else program.run st
          | _       => st
    | Nondet block => block.run st
    | Sequence a b => b.run (a.run st)
    -- Ops
    | Fail => {st with isFailed := true}
    | Set buf offset val =>
        match st.felts val with
          | .some val => st.set! buf offset val
          | _         => st
    | SetGlobal buf offset val =>
        match st.felts val with
          | .some val => st.setGlobal! buf offset val -- Behind the scenes setGlobal actually flattens a 2d buffer into a 1d buffer
          | _         => st                           -- and indexes into it. This is a side effect of global buffers only being 1d anyway

@[simp]
abbrev MLIR.runProgram (program : MLIRProgram) := program.run

notation:61 "Γ " st:max " ⟦" p:49 "⟧" => MLIR.run p st

end Risc0
