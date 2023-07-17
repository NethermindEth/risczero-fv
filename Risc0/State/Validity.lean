import Risc0.State.Defs

namespace Risc0.State

  def varsConsistent (st : State) := ∀ var, var ∈ st.vars ↔ var ∈ st.buffers

  def cycleIsRows (st : State) := ∀ var (h₁ : var ∈ st.buffers), (st.buffers[var].get h₁).length = st.cycle + 1

  def colsConsistent (st : State) := ∀ var, var ∈ st.vars ↔ var ∈ st.bufferWidths

  def bufferLensConsistent (st : State) :=
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

end Risc0.State
