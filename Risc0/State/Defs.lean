import Risc0.Buffer
import Risc0.Cirgen.BasicTypes

import Mathlib.Data.List.Basic

namespace Risc0

  inductive ExternPlonkBuffer | PlonkRows | PlonkAccumRows
  deriving DecidableEq

  instance : ToString ExternPlonkBuffer := ⟨
    (match · with | .PlonkRows => "PlonkRows" | .PlonkAccumRows => "PlonkAccumRows")
  ⟩

  def mangle (table : ExternPlonkBuffer) (discr : BufferVar) : String :=
    toString table ++ discr.name

  lemma mangle_inj'_of_ne (h : discr ≠ discr') : mangle table ⟨discr⟩ ≠ mangle table' ⟨discr'⟩ := by
    simp [mangle]
    rcases discr with ⟨discr⟩; rcases discr' with ⟨discr'⟩
    cases table <;> cases table' <;> simp [toString] <;> intros contra <;> simp at *
    · have : discr = discr' := by
        apply List.append_inj_right (s₁ := "PlonkRows".data) (s₂ := "PlonkRows".data) _ rfl
        injection contra
      aesop
    · injection contra; aesop
    · injection contra; aesop
    · have : discr = discr' := by
        apply List.append_inj_right (s₁ := "PlonkAccumRows".data) (s₂ := "PlonkAccumRows".data) _ rfl
        injection contra
      aesop

  inductive Lit where
    | Buf              : BufferAtTime → Lit
    | Constraint       : Prop         → Lit
    | Val              : Felt         → Lit
    | ExternReadResult : ExternPlonkBuffer → BufferAtTime → Lit

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

  def Buffer.back (st : State) (buf : BufferVar) (back : Back) (offset : ℕ) :=
    st.buffers[buf].get!.get! (st.cycle - back.toNat, offset)

  abbrev withEqZero (x : Felt) (st : State) : State :=
    {st with constraints := (x = 0) :: st.constraints}

  namespace State

    def dropFelts (st: State) (name: FeltVar) : State :=
      { st with felts := st.felts.drop name }

    def updateFelts (state : State) (name : FeltVar) (x : Felt) : State :=
      { state with felts := state.felts[name] ←ₘ x }

    def updateProps (state : State) (name : PropVar) (x : Prop) : State :=
      { state with props := state.props[name] ←ₘ x }

    abbrev SpecialSymbol := '^'

    def isSpecial (str : String) := str.get 0 = SpecialSymbol

    instance : Decidable (isSpecial s) := by unfold isSpecial; exact inferInstance

    lemma isSpecial_toString_SpecialSymbol : isSpecial (toString SpecialSymbol) := by simp [isSpecial]

    private lemma String.get_iff_List_get (s : String) : s.get 0 = s.data.get! 0 := by
      rcases s with ⟨_ | ⟨hd, tl⟩⟩
      · simp
      · simp [String.get, String.utf8GetAux]

    lemma isSpecial_toString_SpecialSymbol_app : isSpecial (toString SpecialSymbol ++ b) := by
      simp [isSpecial, String.get_iff_List_get]

    instance : Decidable (isSpecial s) := by unfold isSpecial; exact inferInstance

    def consecutiveUpdatesFrom (i : ℕ) (name : String) (buf : BufferAtTime) : List (FeltVar × Felt) :=
      (List.range buf.length).map (⟨s!"{SpecialSymbol}{name}#{·+i}"⟩) |>.zip (buf.map Option.get!)

    def consecutiveUpdates (name : String) (buf : BufferAtTime) : List (FeltVar × Felt) :=
      consecutiveUpdatesFrom 0 name buf

    @[simp]
    lemma consecutiveUpdatesFrom_nil : consecutiveUpdatesFrom i name [] = [] := by
      simp [consecutiveUpdatesFrom]

    @[simp]
    lemma consecutiveUpdatesFrom_cons {tl : BufferAtTime} :
      consecutiveUpdatesFrom i name (hd :: tl) =
      ((⟨s!"{SpecialSymbol}{name}#{i}"⟩ : FeltVar), hd.get!) :: consecutiveUpdatesFrom (i + 1) name tl := by
      simp [consecutiveUpdatesFrom, List.range_succ_eq_map]; congr
      funext z
      simp [Nat.succ_add_eq_succ_add]

    @[simp]
    lemma consecutiveUpdates_nil : consecutiveUpdates name [] = [] := by
      simp [consecutiveUpdates, consecutiveUpdatesFrom]

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
                  then {state with buffers := state.buffers[⟨name⟩] ←ₘ oldBuffer.setAllLatest! newBufferAtTime}
                  else {state with isFailed := true}
                | .none        => {state with isFailed := true}
            | .ExternReadResult discr buf => -- TODO(minor): This should be a Sequence of Get, brawl the termination checker later.
              let name := mangle discr ⟨name⟩
              {state with
                 buffers := state.buffers[⟨name⟩] ←ₘ
                              state.buffers[(⟨name⟩ : BufferVar)].get!.popFront
                 felts := Map.updateMany state.felts <| consecutiveUpdates name buf}

    def setBufferElementImpl (st : State) (bufferVar : BufferVar) (idx: Buffer.Idx) (val : Felt) : State :=
      match (st.buffers[bufferVar].get!).set? idx val with
        | .some b => {st with buffers := st.buffers[bufferVar] ←ₘ b}
        | .none   => {st with isFailed := true}

    -- TODO rename, notation
    def set! (st : State) (bufferVar : BufferVar) (offset : ℕ) (val : Felt) : State :=
      st.setBufferElementImpl bufferVar (((st.buffers[bufferVar].get!).length - 1), offset) val

    def setMany! (st : State) (buf : BufferVar) (felts : List FeltVar) : State :=
      (·.1) <| felts.foldl
        (init := (st, 0))
        λ (acc, i) feltVar ↦ (acc.set! buf i st.felts[feltVar].get!, i + 1)

    -- TODO remove lets
    def setGlobal! (st : State) (bufferVar : BufferVar) (offset : ℕ) (val : Felt) : State :=
      let width := st.bufferWidths[bufferVar].get!
      st.setBufferElementImpl bufferVar (Buffer.Idx.from1D offset width) val

    def allocateBuffer (st : State) (buf : BufferVar) : State :=
      if buf ∈ st.buffers
      then st
      else {
        st with buffers := st.buffers[buf] ←ₘ Buffer.empty
                vars := buf :: st.vars
                bufferWidths := st.bufferWidths[buf] ←ₘ 0
      }

    def allocateBufferRow (st : State) (buf : BufferVar) (n : ℕ) : State :=
      if buf ∈ st.buffers
      then { st with buffers := st.buffers[buf] ←ₘ
                                  st.buffers[buf].get!.push (BufferAtTime.init n)
                     bufferWidths := st.bufferWidths[buf] ←ₘ n }
      else st

    def allocateBufferRow! (st : State) (buf : BufferVar) (n : ℕ) : State :=
      allocateBufferRow (st.allocateBuffer buf) buf n

  end State


end Risc0
