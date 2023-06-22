--Overall proof plan

-- pre st → Constraints ( Witness (st))
-- st.isValid → (Constraints st ↔ spec (e.g. (input=0, is0=1) ∨ (input≠0, is0=0, inv=input⁻¹)))
-- where
-- pre st = st.isValid ∧ ...
-- Constraints st = (runConstraints st).getReturn ∧ (runConstraints st).isValid
-- Witness st = runWitness st
--  do we need at add |>.clearTemporaries ?

-- to prove Constraints st, we want to actually prove
--  (runConstraints st).isValid ∧ ((runConstraints st).isValid → (runConstraints st).getReturn)
--  utilising the lemma (to prove) that a state cannot be/become valid after an invalid get