import Risc0.Buffer

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

  end State

end Risc0
