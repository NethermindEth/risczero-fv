import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.FieldSimp

import Risc0.Basic
import Risc0.Lemmas
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Axioms

namespace Risc0.OneHot.WitnessParts

namespace Setup0

lemma get_back_zero_is_last {st: State} {input : Felt} {offset : ℕ} {name : String} (h_valid: st.WellFormed) (h_var: ⟨name⟩ ∈ st.vars):
  (st.buffers.get! ⟨name⟩).get! (st.cycle - Back.toNat 0, offset)
  =
  (st.buffers.get! ⟨name⟩).last!.get! offset := by
  have h_buffername: ⟨name⟩ ∈ st.buffers := h_valid.hVars ⟨name⟩ |>.mp h_var
  have h_back0: st.cycle - Back.toNat 0 = st.cycle := by aesop
  rewrite [h_back0]
  unfold Buffer.get!
  simp only [Buffer.Idx.time, Buffer.Idx.data, Buffer.last!]
  have h_cycle: (st.buffers.get! ⟨name⟩).length = st.cycle + 1 := sorry
  sorry




lemma closed_form {input : Felt} (st: State) :
  pre st input → post (prog.run st) input := by
  intro h_pre
  unfold prog
  MLIR_statement
  simp only [Op.eval_const, State.update_val]
  MLIR_statement
  simp only [Op.eval_const, State.update_val]
  MLIR_statement
  simp only [Op.eval_const, State.update_val, Op.eval_getBuffer]
  rewrite [MLIR.run_valid_get, State.update]
  simp only [ge_iff_le]
  generalize hs₁ : {st with felts := (((st.felts[⟨"2"⟩] := 2)[⟨"1"⟩] := 1)[⟨"0"⟩] := 0)[⟨"input"⟩] := ((st.buffers.get! ⟨"input"⟩).get! (st.cycle - Back.toNat 0, 0)).get!} = s₁
  unfold post
  unfold pre at h_pre

end Setup0

end Risc0.OneHot.WitnessParts