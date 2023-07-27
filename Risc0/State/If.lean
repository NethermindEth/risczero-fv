import Risc0.State.Defs

namespace Risc0.State

  lemma buffers_if_eq {c} [Decidable c] {st st' : State} (h : st.buffers = st'.buffers) :
    State.buffers (if c then st else st') = st.buffers := by aesop'

  lemma bufferWidths_if_eq {c} [Decidable c] {st st' : State} (h : st.bufferWidths = st'.bufferWidths) :
    State.bufferWidths (if c then st else st') = st.bufferWidths := by aesop'

  lemma cycle_if_eq {c} [Decidable c] {st st' : State} (h : st.cycle = st'.cycle) :
    State.cycle (if c then st else st') = st.cycle := by aesop'

  lemma felts_if_eq {c} [Decidable c] {st st' : State} (h : st.felts = st'.felts) :
    State.felts (if c then st else st') = st.felts := by aesop'

  lemma isFailed_if_eq {c} [Decidable c] {st st' : State} (h : st.isFailed = st'.isFailed) :
    State.isFailed (if c then st else st') = st.isFailed := by aesop'

  lemma props_if_eq {c} [Decidable c] {st st' : State} (h : st.props = st'.props) :
    State.props (if c then st else st') = st.props := by aesop'

  lemma vars_if_eq {c} [Decidable c] {st st' : State} (h : st.vars = st'.vars) :
    State.vars (if c then st else st') = st.vars := by aesop'

  lemma buffers_if_eq_if_buffers [Decidable c] :
    State.buffers (if c then st else st') = if c then st.buffers else st'.buffers := by
      aesop'

  lemma bufferWidths_if_eq_if_bufferWidths [Decidable c] :
    State.bufferWidths (if c then st else st') = if c then st.bufferWidths else st'.bufferWidths := by
      aesop'

  lemma cycle_if_eq_if_cycle [Decidable c] :
    State.cycle (if c then st else st') = if c then st.cycle else st'.cycle := by
      aesop'

  lemma felts_if_eq_if_felts [Decidable c] :
    State.felts (if c then st else st') = if c then st.felts else st'.felts := by
      aesop'

  lemma isFailed_if_eq_if_isFailed [Decidable c] :
    State.isFailed (if c then st else st') = if c then st.isFailed else st'.isFailed := by
      aesop'

  lemma props_if_eq_if_props [Decidable c] :
    State.props (if c then st else st') = if c then st.props else st'.props := by
      aesop'

  lemma vars_if_eq_if_vars [Decidable c] :
    State.vars (if c then st else st') = if c then st.vars else st'.vars := by
      aesop'

end Risc0.State
