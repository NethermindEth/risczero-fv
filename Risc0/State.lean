import Risc0.Basic
import Risc0.Buffer

namespace Risc0

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

inductive Lit where
  | Buf        : BufferAtTime → Lit
  | Constraint : Prop         → Lit
  | Val        : Felt         → Lit

namespace State

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

abbrev Input := "input"
abbrev Output := "output"

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

notation:61 st "[felts][" n:61 "]" " ← " x:49 => State.updateFelts st n x

def updateProps (state : State) (name : PropVar) (x : Prop) : State :=
  { state with props := state.props[name] ←ₘ x }

notation:61 st "[props][" n:61 "]" " ← " x:49 => State.updateProps st n x

lemma updateFelts_def : 
  updateFelts st k v = { st with felts := st.felts[k] ←ₘ v } := rfl

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

@[simp]
lemma updateFelts_felts : (updateFelts st name x).felts = st.felts[name] ←ₘ x := by simp [updateFelts]

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

@[simp]
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

def get_back (buf : BufferVar) (back : Back) (offset : ℕ) :=
  st.buffers[buf].get!.get! (st.cycle - back.toNat, offset)

lemma get_back_def {st : State} {buf : BufferVar} {back : Back} :
  State.get_back st buf back offset = st.buffers[buf].get!.get! (st.cycle - back.toNat, offset) := rfl

abbrev withEqZero (x : Felt) : State :=
  {st with constraints := (x = 0) :: st.constraints}

@[simp]
lemma withEqZero_def : withEqZero st x = {st with constraints := (x = 0) :: st.constraints} := rfl

def setBufferElementImpl (bufferVar : BufferVar) (idx: Buffer.Idx) (val : Felt) : State :=
  match (st.buffers[bufferVar].get!).set? idx val with
    | .some b => {st with buffers := st.buffers[bufferVar] ←ₘ b}
    | .none   => {st with isFailed := true}

def set! (bufferVar : BufferVar) (offset : ℕ) (val : Felt) : State :=
  st.setBufferElementImpl bufferVar (((st.buffers[bufferVar].get!).length - 1), offset) val

@[simp]
lemma set!_felts {st : State} {bufferVar : BufferVar} {offset : ℕ} {val : Felt} :
  (State.set! st bufferVar offset val).felts = st.felts := by
  unfold set! setBufferElementImpl
  aesop

def setGlobal! (bufferVar : BufferVar) (offset : ℕ) (val : Felt) : State :=
  let width := st.bufferWidths[bufferVar].get!
  st.setBufferElementImpl bufferVar (Buffer.Idx.from1D offset width) val

end State

instance : Inhabited State := ⟨State.init_default 42 42⟩

notation:61 st "[" n:61 "]" " ←ₛ " x:49 => State.update st n x

end Risc0
