import Risc0.State.UpdateFelts
import Risc0.State.UpdateProps

namespace Risc0.State

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
  private lemma updateMany_consecutiveUpdates_of_ne {m : Map FeltVar Felt}
    (h : ¬isSpecial name') :
    (m.updateMany (consecutiveUpdates name l)) (⟨name'⟩ : FeltVar) = m (⟨name'⟩ : FeltVar) := by
    simp [consecutiveUpdates]
    generalize 0 = k
    induction l generalizing k with
      | nil => simp
      | cons hd tl ih => simp; rw [Map.update_get_next', ih]; simp
                         rintro ⟨contra⟩
                         exact absurd (isSpecial_toString_SpecialSymbol_app) h

  @[simp]
  lemma update_skip_felts (h: name' ≠ name) (h' : ¬isSpecial name):
    (State.felts (update st name' x) { name }) = (State.felts st { name }) := by
      simp only [State.update]
      aesop

  @[simp]
  lemma update_skip_nested_felts (h: name' ≠ name) (h' : ¬isSpecial name):
    (State.felts (update ( update st name' x) name y) { name }) = (State.felts (update st name y) { name }) := by
    simp [h, State.update]
    aesop'

end Risc0.State
