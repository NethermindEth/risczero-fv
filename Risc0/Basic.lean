import Mathlib.Data.Nat.Prime
import Mathlib.Data.Finmap
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Bitvec.Basic

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

abbrev Idx := ℕ × ℕ -- time, data
abbrev Idx.time : Idx → ℕ := Prod.fst
abbrev Idx.data : Idx → ℕ := Prod.snd

def empty : Buffer := []

def init (size : ℕ) : Buffer := [List.replicate size .none]

def init' (row : BufferAtTime) : Buffer := [row]

def last! (buf : Buffer) : BufferAtTime :=
  buf.getLast!

def copyLast (buf : Buffer) : Buffer := 
  buf.push buf.last!

def get! (buf : Buffer) (idx : Idx) : Option Felt :=
  List.get! (List.get! buf idx.time) idx.data

-- @[simp]
-- lemma www : buffer.get! [[some ...]] (0...k)

def getBufferAtTime! (buf : Buffer) (timeIdx : ℕ) : BufferAtTime :=
  List.get! buf timeIdx

def setAllLatest! (buf : Buffer) (val : BufferAtTime) : Buffer :=
  List.set buf (buf.length - 1) val

def set? (buf : Buffer) (idx: Idx) (val: Felt) : Option Buffer :=
  let bufferAtTime := buf.getBufferAtTime! idx.time
  let oldVal := (bufferAtTime.get! idx.data)
  if oldVal.isEqSome val
  then .some buf
  else
    if oldVal.isNone
    then .some <| List.set buf idx.time (bufferAtTime.set idx.data (.some val))
    else .none

def isValidUpdate (old new : BufferAtTime) :=
  old.length = new.length ∧
  (List.zip old new).all
    λ (oldElem, newElem) =>
      oldElem.isNone ∨
      oldElem = newElem

instance {old new} : Decidable (Buffer.isValidUpdate old new) := by
  unfold Buffer.isValidUpdate
  exact inferInstance

def Idx.from1D (flatOffset width : ℕ) : Idx :=
  (flatOffset.div width, flatOffset.mod width)

lemma data_idx_le_width (flatOffset width : ℕ) (h: width > 0) : (Idx.from1D flatOffset width).data < width :=
  Nat.mod_lt _ h

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

def empty : State :=
  {
    buffers := Map.empty
    bufferWidths := Map.empty,
    constraints := [],
    cycle := 0, -- should cycle actually equal zero here or should it be arbitrary?
    felts := Map.empty,
    props := Map.empty,
    vars := [],
    isFailed := false,
  }

def addBuffer (name: String) (buffer: Buffer): State :=
  { st with
    buffers := st.buffers[⟨name⟩] ←ₘ buffer,
    bufferWidths := st.bufferWidths[⟨name⟩] ←ₘ buffer.last!.length,
    vars := ⟨name⟩ :: st.vars
  }

def hasFelts (felts: List (String × Felt)) : Prop :=
  match felts with
  | [] => True
  | (name, value) :: fs =>
    st.felts[(⟨name⟩ : FeltVar)]!.get! = value ∧
    hasFelts fs

def varsConsistent := ∀ var, var ∈ st.vars ↔ var ∈ st.buffers

def cycleIsRows := ∀ var (h₁ : var ∈ st.buffers), (st.buffers[var].get h₁).length = st.cycle + 1

def colsConsistent := ∀ var, var ∈ st.vars ↔ var ∈ st.bufferWidths

def bufferLensConsistent :=
  ∀ var (h : var ∈ st.buffers) (h₁ : cycleIsRows st),
    ∀ row (h₂ : row ≤ st.cycle),
      have : row < (st.buffers[var].get h).length := by rw [h₁]; linarith
      st.bufferWidths var = (st.buffers[var].get h)[row].length

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
  
def Valid (st : State) := st.WellFormed ∧ ¬st.isFailed

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

def lastOutput (st : State) :=
  st.buffers ⟨Output⟩ |>.get!.getLast!

def constraintsInVar (st : State) (var : PropVar) :=
  st.props var |>.getD True

-- Only used to prove State inhabited, since it initialises both input and output as write-only
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
      λ h => by simp [init] at *; simp [Map.mem_def, Map.update, Map.getElem_def] at h; split at h <;> aesop 
    ⟩ 
  hCycle   := λ var h =>
    by have : var = ⟨Input⟩ ∨ var = ⟨Output⟩ := by
         simp only [init] at h; rw [Map.mem_fromList] at h; simp at h; exact h
       rcases this with h | h <;> subst h <;> simp [Map.getElem_def] <;> rfl
  hCols    := λ var => ⟨
      λ h => by simp [init] at h; rcases h with h | h <;> subst h ; decide_mem_map,
      λ h => by simp [init] at h ⊢; simp [Map.mem_def, Map.update, Map.getElem_def] at h; aesop
    ⟩ 
  hColsLen := valid_init'_aux

lemma valid_init : (init_default m n).WellFormed := valid_init'

def update (state : State) (name : String) (x : Option Lit) : State :=
  match x with
    | .none => {state with isFailed := true}
    | .some lit =>
      match lit with
        | .Constraint c => {state with props := state.props[⟨name⟩] ←ₘ c}
        | .Val        x => {state with felts := state.felts[⟨name⟩] ←ₘ x}
        | @Lit.Buf    newBufferAtTime =>
          match state.buffers ⟨name⟩ with
            | .some oldBuffer =>
              if Buffer.isValidUpdate oldBuffer.last! newBufferAtTime
              then {state with buffers := state.buffers[⟨name⟩] ←ₘ (oldBuffer.setAllLatest! newBufferAtTime)}
              else {state with isFailed := true}
            | .none        => {state with isFailed := true}

def updateFelts (state : State) (name : FeltVar) (x : Felt) : State :=
  { state with felts := state.felts[name] ←ₘ x }

def dropFelts (st : State) (name : FeltVar) : State :=
  { st with felts := st.felts.drop name }

@[simp]
lemma drop_update_same {st : State} {name : FeltVar} {x : Felt} : 
  dropFelts (updateFelts st name x) name = dropFelts st name := by
  simp [dropFelts, updateFelts]

@[simp]
lemma drop_update_swap {st : State} {name name' : FeltVar} {x : Felt} (h : name ≠ name') :
  dropFelts (updateFelts st name x) name' = updateFelts (dropFelts st name') name x := by
  simp [dropFelts, updateFelts]
  exact Map.update_drop_swap h

notation:61 st:max "[felts][" n:61 "]" " ← " x:49 => State.updateFelts st n x

def updateProps (state : State) (name : PropVar) (x : Prop) : State :=
  { state with props := state.props[name] ←ₘ x }

notation:61 st:max "[props][" n:61 "]" " ← " x:49 => State.updateProps st n x

lemma updateFelts_def : 
  updateFelts st k v = { st with felts := st.felts[k] ←ₘ v } := rfl

lemma dropFelts_def :
  dropFelts st k = { st with felts := st.felts.drop k } := rfl

lemma updateProps_def :
  updateProps st k v = { st with props := st.props[k] ←ₘ v } := rfl

@[simp]
lemma updateFelts_felts_get {st : State} {name : FeltVar} {x : Felt} :
  (updateFelts st name x).felts[name]! = some x := by
  simp [updateFelts, Map.update_def, Map.getElem_def, getElem!]

@[simp]
lemma updateProps_props_get {st : State} {name : PropVar} {x : Prop} :
  (updateProps st name x).props[name]! = some x := by
  simp [updateProps, Map.update_def, Map.getElem_def, getElem!]

-- @[simp]
-- lemma updateFelts_props {st : State} {name : FeltVar} {x : Felt} :
--   (st[felts][name] ← x).props = st.props := by simp [updateFelts]

-- @[simp]
-- lemma updateProps_felts {st : State} {name : PropVar} {x : Prop} :
--   (st[props][name] ← x).felts = st.felts := by simp [updateProps]

-- TODO: This technically shouldn't exist, refine later?
-- m[k] should not unfold to m k, yet there are instances in automated rewriting
-- where this somehow occurs.
@[simp]
lemma updateFelts_felts_get_wobbly {st : State} {name : FeltVar} {x : Felt} :
  (updateFelts st name x).felts name = some x := updateFelts_felts_get

@[simp]
lemma updateProps_props_get_wobbly {st : State} {name : PropVar} {x : Prop} :
  (updateProps st name x).props name = some x := updateProps_props_get

-- This simp lemma feels bad with name ≠ name' but somehow it works out in our context.
@[simp]
lemma updateFelts_felts_get_ne {st : State} {name name' : FeltVar} {x : Felt}
  (h : name ≠ name') : (updateFelts st name x).felts[name']! = st.felts[name']! := by
  simp [updateFelts, Map.update_def, getElem!, Map.getElem_def]
  aesop

-- This simp lemma feels bad with name ≠ name' but somehow it works out in our context.
@[simp]
lemma updateProps_props_get_ne {st : State} {name name' : PropVar} {x : Prop}
  (h : name ≠ name') : (updateProps st name x).props[name']! = st.props[name']! := by
  simp [updateProps, Map.update_def, getElem!, Map.getElem_def]
  aesop

@[simp]
lemma updateFelts_buffers : (updateFelts st name x).buffers = st.buffers := by simp [updateFelts]

@[simp]
lemma updateFelts_bufferWidths : (updateFelts st name x).bufferWidths = st.bufferWidths := by simp [updateFelts]

@[simp]
lemma updateFelts_constraints : (updateFelts st name x).constraints = st.constraints := by simp [updateFelts]

@[simp]
lemma updateFelts_cycle : (updateFelts st name x).cycle = st.cycle := by simp [updateFelts]

@[simp]
lemma updateFelts_isFailed : (updateFelts st name x).isFailed = st.isFailed := by simp [updateFelts]

@[simp]
lemma updateFelts_props : (updateFelts st name x).props = st.props := by simp [updateFelts]

@[simp]
lemma updateFelts_vars : (updateFelts st name x).vars = st.vars := by simp [updateFelts]

-- @[simp]
lemma updateFelts_felts : (updateFelts st name x).felts = st.felts[name] ←ₘ x := by simp [updateFelts]

@[simp]
lemma updateFelts_felts_get_next (h: name ≠ name') : (updateFelts st name x).felts name' = st.felts name' := by
  simp [updateFelts]
  exact Map.update_get_next' h

@[simp]
lemma updateProps_buffers : (updateProps st name x).buffers = st.buffers := by simp [updateProps]

@[simp]
lemma updateProps_bufferWidths : (updateProps st name x).bufferWidths = st.bufferWidths := by simp [updateProps]

@[simp]
lemma updateProps_constraints : (updateProps st name x).constraints = st.constraints := by simp [updateProps]

@[simp]
lemma updateProps_cycle : (updateProps st name x).cycle = st.cycle := by simp [updateProps]

@[simp]
lemma updateProps_isFailed : (updateProps st name x).isFailed = st.isFailed := by simp [updateProps]

@[simp]
lemma updateProps_felts : (updateProps st name x).felts = st.felts := by simp [updateProps]

@[simp]
lemma updateProps_vars : (updateProps st name x).vars = st.vars := by simp [updateProps]

-- @[simp]
lemma updateProps_props : (updateProps st name x).props = st.props[name] ←ₘ x := by simp [updateProps]

-- @[simp]
lemma update_val {state : State} {name : String} {x : Felt} :
  update state name (.some (.Val x)) = { state with felts := state.felts[⟨name⟩] ←ₘ x } := rfl

lemma update_constr {state : State} {name : String} {x : Prop} :
  update state name (.some (.Constraint x)) = { state with props := state.props[⟨name⟩] ←ₘ x } := rfl

@[simp]
lemma update_val' {state : State} {name : String} {x : Felt} :
  update state name (.some (.Val x)) = state.updateFelts ⟨name⟩ x := rfl

@[simp]
lemma update_constr' {state : State} {name : String} {x : Prop} :
  update state name (.some (.Constraint x)) = state.updateProps ⟨name⟩ x := rfl

-- @[simp]
lemma update_constraint {state : State} {name : String} {c : Prop} :
  update state name (.some (.Constraint c)) = { state with props := state.props.update ⟨name⟩ c } := rfl

@[simp]
lemma update_skip_felts (h: name' ≠ name) :
  (State.felts
    (update st name' x)
    { name }) =
  (State.felts st { name }) := by
    simp only [State.update]
    aesop
    simp [State.update, ←Map.getElem_def, Map.update_get_next, h]

@[simp]
lemma update_skip_nested_felts (h: name' ≠ name) :
  (State.felts
    (update ( update st name' x) name y)
    { name }) =
  (State.felts
    (update st name y)
    { name }) := by
  simp [h, State.update]
  aesop
  all_goals simp [h, ←Map.getElem_def, Map.update_get_next]

@[simp]
lemma if_constraints {state₁ state₂ : State} {x : Felt} :
  (if x = 0 then state₁ else state₂).constraints =
  if x = 0 then state₁.constraints else state₂.constraints := by apply apply_ite

lemma buffers_if {c} [Decidable c] {st st' : State} (h : st.buffers = st'.buffers) :
  State.buffers (if c then st else st') = st.buffers := by aesop

lemma bufferWidths_if {c} [Decidable c] {st st' : State} (h : st.bufferWidths = st'.bufferWidths) :
  State.bufferWidths (if c then st else st') = st.bufferWidths := by aesop

lemma constraints_if {c} [Decidable c] {st st' : State} (h : st.constraints = st'.constraints) :
  State.constraints (if c then st else st') = st.constraints := by aesop

lemma cycle_if {c} [Decidable c] {st st' : State} (h : st.cycle = st'.cycle) :
  State.cycle (if c then st else st') = st.cycle := by aesop

lemma felts_if {c} [Decidable c] {st st' : State} (h : st.felts = st'.felts) :
  State.felts (if c then st else st') = st.felts := by aesop

lemma isFailed_if {c} [Decidable c] {st st' : State} (h : st.isFailed = st'.isFailed) :
  State.isFailed (if c then st else st') = st.isFailed := by aesop

lemma props_if {c} [Decidable c] {st st' : State} (h : st.props = st'.props) :
  State.props (if c then st else st') = st.props := by aesop

lemma vars_if {c} [Decidable c] {st st' : State} (h : st.vars = st'.vars) :
  State.vars (if c then st else st') = st.vars := by aesop

end State

end State

instance : Inhabited State := ⟨State.init_default 42 42⟩

notation:61 st:max "[" n:61 "]" " ←ₛ " x:49 => State.update st n x

namespace State

variable {st : State}

-- TODO: Rework to updateConstraints (done?)
-- @[simp]
-- lemma updateConstraints_buffers {st : State} :
--   (st[k] ←ₛ some (Lit.Constraint c)).buffers = st.buffers := by simp [State.update]

-- @[simp]
-- lemma updateConstraints_bufferWidths :
--   (st[k] ←ₛ some (Lit.Constraint c)).bufferWidths = st.bufferWidths := by simp [State.update]

-- @[simp]
-- lemma updateConstraints_felts :
--   (st[k] ←ₛ some (Lit.Constraint c)).felts = st.felts := by simp [State.update]

-- @[simp]
-- lemma updateConstraints_cycle :
--   (st[k] ←ₛ some (Lit.Constraint c)).cycle = st.cycle := by simp [State.update]

-- @[simp]
-- lemma updateConstraints_isFailed :
--   (st[k] ←ₛ some (Lit.Constraint c)).isFailed = st.isFailed := by simp [State.update]

-- @[simp]
-- lemma updateConstraints_vars :
--   (st[k] ←ₛ some (Lit.Constraint c)).vars = st.vars := by simp [State.update]


-- @[simp]
-- lemma set_felts {st : State} {name : String} {x} :
--   (st[name] ←ₛ some (Lit.Val x)).felts = _ := _

end State

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
  | BitAnd : FeltVar → FeltVar → Op x
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

-- Naughty
@[simp]
lemma State.get_dropFelts_of_ne {st : State} {x : FeltVar} (h : name ≠ x) :
  Option.get! (st.dropFelts name).felts[x] = Option.get! st.felts[x] := by
  unfold State.dropFelts Map.drop
  rw [Map.getElem_def]
  aesop

def BufferAtTime.slice (buf : BufferAtTime) (offset size : ℕ) : BufferAtTime :=
  buf.drop offset |>.take size

def rowColOfWidthIdx (width idx : ℕ) : Back × ℕ := (idx / width, idx % width)

lemma col_lt_width (h : 0 < width) : (rowColOfWidthIdx width idx).2 < width := Nat.mod_lt _ h

def Buffer.back (st : State) (buf : BufferVar) (back : Back) (offset : ℕ) :=
  st.buffers[buf].get!.get! (st.cycle - back.toNat, offset)

lemma Buffer.back_def {st : State} {buf : BufferVar} {back : Back} :
  Buffer.back st buf back offset = st.buffers[buf].get!.get! (st.cycle - back.toNat, offset) := rfl

def isGetValid (st : State) (buf : BufferVar) (back : Back) (offset : ℕ) :=
  back ≤ st.cycle ∧
  buf ∈ st.vars ∧
  offset < st.bufferWidths[buf].get! ∧
  (Buffer.back st buf back offset).isSome

lemma isGetValid_def :
  isGetValid st buf back offset = 
  (back ≤ st.cycle ∧
   buf ∈ st.vars ∧
   offset < st.bufferWidths[buf].get! ∧
   (Buffer.back st buf back offset).isSome) := rfl

instance : Decidable (isGetValid st buf back offset) := by unfold isGetValid; exact inferInstance

def getImpl (st : State) (buf : BufferVar) (back : Back) (offset : ℕ) :=
  if isGetValid st buf back offset
  then Option.some <| Lit.Val (Buffer.back st buf back offset).get!
  else .none

lemma getImpl_def : getImpl st buf back offset = 
                    if isGetValid st buf back offset
                    then Option.some <| Lit.Val (Buffer.back st buf back offset).get!
                    else .none := rfl

--Review: should any of these be simps?
lemma getImpl_none_or_val : getImpl st buf back offset = .none ∨ ∃ x, getImpl st buf back offset = some (.Val x) := by
  simp [getImpl]
  aesop

lemma getImpl_val_of_some : getImpl st buf back offset = some lit → ∃ x, lit = .Val x := by
  have h: getImpl st buf back offset = .none ∨ ∃ x, getImpl st buf back offset = some (.Val x) := getImpl_none_or_val
  aesop

lemma getImpl_skip_none_update : getImpl (st[name] ←ₛ .none) buf back offset = getImpl st buf back offset := by
  simp [State.update, getImpl, isGetValid, Buffer.back]

lemma getImpl_skip_val_update : getImpl (st[name] ←ₛ .some (.Val x)) buf back offset = getImpl st buf back offset := by
  simp [State.update, getImpl, isGetValid, Buffer.back]

@[simp]
lemma getImpl_skip_get_update:
  getImpl (st[name] ←ₛ getImpl st' buf' back' offset') buf back offset =
  getImpl st buf back offset := by
  generalize eq: getImpl st' buf' back' offset' = x
  cases x with
   | none => exact getImpl_skip_none_update
   | some lit =>
    have h: ∃ x, lit = Lit.Val x := getImpl_val_of_some eq
    aesop

def feltBitAnd (x y: Felt) : Felt :=
  ↑(Bitvec.and (Bitvec.ofNat 256 x.val) (Bitvec.ofNat 256 y.val)).toNat


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
    | BitAnd lhs rhs => .some <| .Val <| feltBitAnd st.felts[lhs].get! st.felts[rhs].get!
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
  let val := (st.buffers[buf].get!).get! ((st.cycle - back.toNat), offset)
  if back ≤ st.cycle ∧ buf ∈ st.vars ∧ offset < st.bufferWidths[buf].get! ∧ val.isSome
  then .some (.Val val.get!)
  else .none := rfl

@[simp]
lemma eval_add : Γ st ⟦@Add α x y⟧ₑ = .some (.Val ((st.felts x).get! + (st.felts y).get!)) := rfl

@[simp]
lemma eval_sub : Γ st ⟦@Sub α x y⟧ₑ = .some (.Val ((st.felts x).get! - (st.felts y).get!)) := rfl

@[simp]
lemma eval_neg : Γ st ⟦@Neg α x⟧ₑ = .some (.Val (0 - (st.felts x).get!)) := rfl

@[simp]
lemma eval_mul : Γ st ⟦@Mul α x y⟧ₑ = .some (.Val ((st.felts x).get! * (st.felts y).get!)) := rfl

@[simp]
lemma eval_isz : Γ st ⟦??₀x⟧ₑ = .some (.Val (if (st.felts x).get! = 0 then 1 else 0)) := rfl

@[simp]
lemma eval_inv : Γ st ⟦Inv x⟧ₑ = .some (.Val (if st.felts[x].get! = 0 then 0 else st.felts[x].get!⁻¹)) := rfl

@[simp]
lemma eval_andEqz : Γ st ⟦@AndEqz α c x⟧ₑ =
                    .some (.Constraint ((st.props c).get! ∧ (st.felts x).get! = 0)) := rfl

@[simp]
lemma eval_pow : Γ st ⟦@Pow α x n⟧ₑ = .some (.Val (st.felts[x].get! ^ n)) := rfl

@[simp]
lemma eval_bitAnd :
  Γ st ⟦@BitAnd α x y⟧ₑ =
    (.some <| .Val <| feltBitAnd (st.felts[x]).get! (st.felts[y]).get!) := rfl

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
  | DropFelt  : FeltVar                → MLIR x
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
scoped prefix  :52                    "dropfelt "                 => MLIR.DropFelt
scoped notation:51                    "guard " c " then " x:51   => MLIR.If c x
scoped prefix  :max                   "nondet"                   => MLIR.Nondet
scoped infixr  :50                    "; "                       => MLIR.Sequence
scoped notation:51 (priority := high) b "[" v:51 "]" " ←ᵢ " x:51 => MLIR.Set b v x

end MLIRNotation

abbrev MLIRProgram := MLIR NotInNondet

abbrev withEqZero (x : Felt) (st : State) : State :=
  {st with constraints := (x = 0) :: st.constraints}

lemma withEqZero_def : withEqZero x st = {st with constraints := (x = 0) :: st.constraints} := rfl

def State.setBufferElementImpl (st : State) (bufferVar : BufferVar) (idx: Buffer.Idx) (val : Felt) : State :=
  match (st.buffers[bufferVar].get!).set? idx val with
    | .some b => {st with buffers := st.buffers[bufferVar] ←ₘ b}
    | .none   => {st with isFailed := true}

def State.set! (st : State) (bufferVar : BufferVar) (offset : ℕ) (val : Felt) : State :=
  st.setBufferElementImpl bufferVar (((st.buffers[bufferVar].get!).length - 1), offset) val

@[simp]
lemma State.set!_felts {st : State} {bufferVar : BufferVar} {offset : ℕ} {val : Felt} :
  (State.set! st bufferVar offset val).felts = st.felts := by
  unfold set! setBufferElementImpl
  aesop

def State.setGlobal! (st : State) (bufferVar : BufferVar) (offset : ℕ) (val : Felt) : State :=
  let width := st.bufferWidths[bufferVar].get!
  st.setBufferElementImpl bufferVar (Buffer.Idx.from1D offset width) val

-- Step through the entirety of a `MLIR` MLIR program from initial state
-- `state`, yielding the post-execution state and possibly a constraint
-- (`Prop`), the return value of the program.
def MLIR.run {α : IsNondet} (program : MLIR α) (st : State) : State :=
  match program with
    -- Meta
    | Assign name op => st[name] ←ₛ Γ st ⟦op⟧ₑ
    | DropFelt k     => .dropFelts st k
    | Eqz x          => withEqZero st.felts[x]!.get! st
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

notation:61 "Γ " st:max " ⟦" p:49 "⟧" => MLIR.run p st

open MLIRNotation

end Risc0
