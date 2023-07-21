import Risc0.State.Defs

namespace Risc0

  lemma withEqZero_def : withEqZero x st = {st with constraints := (x = 0) :: st.constraints} := rfl

  lemma withEqZero_updateFelts :
    withEqZero y (State.updateFelts st name x) = State.updateFelts (withEqZero y st) name x := by
    aesop

  lemma withEqZero_buffers :
    (withEqZero x st).buffers = st.buffers := by
    aesop

  lemma withEqZero_bufferWidths :
    (withEqZero x st).bufferWidths = st.bufferWidths := by
    aesop

  lemma withEqZero_constraints :
    (withEqZero x st).constraints = (x = 0) :: st.constraints := by
    aesop

  lemma withEqZero_cycle :
    (withEqZero x st).cycle = st.cycle := by
    aesop

  lemma withEqZero_felts :
    (withEqZero x st).felts = st.felts := by
    aesop

  lemma withEqZero_isFailed :
    (withEqZero x st).isFailed = st.isFailed := by
    aesop

  lemma withEqZero_props :
    (withEqZero x st).props = st.props := by
    aesop

  lemma withEqZero_vars :
    (withEqZero x st).vars = st.vars := by
    aesop

end Risc0
