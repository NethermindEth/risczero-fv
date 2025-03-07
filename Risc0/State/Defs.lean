import Risc0.Buffer
import Risc0.Cirgen.BasicTypes

namespace Risc0

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
    -- constraints  : List Prop
    -- Current cycle.
    cycle        : ℕ
    -- Temporary felts.
    felts        : Map FeltVar Felt
    -- Is the state invalid.
    isFailed     : Prop
    -- Context of propositions.
    props        : Map PropVar Prop
    -- Valid variables for buffers.
    vars         : List BufferVar

  abbrev Input := "input"
  abbrev Output := "output"

  def Buffer.back (st : State) (buf : BufferVar) (back : Back) (offset : ℕ) :=
    st.buffers[buf].get!.get! (st.cycle - back.toNat, offset)

  abbrev withEqZero (x : Felt) (st : State) : State :=
    {st with isFailed := st.isFailed ∨ (x ≠ 0)}

  namespace State

    def dropFelts (st: State) (name: FeltVar) : State :=
      { st with felts := st.felts.drop name }

    def updateFelts (state : State) (name : FeltVar) (x : Felt) : State :=
      { state with felts := state.felts[name] ←ₘ x }

    def updateProps (state : State) (name : PropVar) (x : Prop) : State :=
      { state with props := state.props[name] ←ₘ x }

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

    def setBufferElementImpl (st : State) (bufferVar : BufferVar) (idx: Buffer.Idx) (val : Felt) : State :=
      match (st.buffers[bufferVar].get!).set? idx val with
        | .some b => {st with buffers := st.buffers[bufferVar] ←ₘ b}
        | .none   => {st with isFailed := true}

    lemma setBufferElementImpl_def : setBufferElementImpl st bufferVar idx val = 
      match (st.buffers[bufferVar].get!).set? idx val with
        | .some b => {st with buffers := st.buffers[bufferVar] ←ₘ b}
        | .none   => {st with isFailed := true} := rfl

    -- TODO rename, notation
    def set! (st : State) (bufferVar : BufferVar) (offset : ℕ) (val : Felt) : State :=
      st.setBufferElementImpl bufferVar (((st.buffers[bufferVar].get!).length - 1), offset) val

    -- TODO remove let
    def setGlobal! (st : State) (bufferVar : BufferVar) (offset : ℕ) (val : Felt) : State :=
      let width := st.bufferWidths[bufferVar].get!
      st.setBufferElementImpl bufferVar (Buffer.Idx.from1D offset width) val
  end State


end Risc0
