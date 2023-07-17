import Risc0.Cirgen.Notation

namespace Risc0.Op

open MLIRNotation

@[simp]
lemma eval_const : Γ st ⟦@Const α x⟧ₑ = .some (.Val x) := rfl

@[simp]
lemma eval_true : Γ st ⟦@Op.True α⟧ₑ = .some (.Constraint (_root_.True)) := rfl

@[simp]
lemma eval_getBuffer : Γ st ⟦@Get α buf back offset⟧ₑ =
  let val := (st.buffers[buf].get!).get! ((st.cycle - back.toNat), offset)
  if back ≤ st.cycle ∧ buf ∈ st.vars ∧ offset < st.bufferWidths[buf].get! ∧ val.isSome
  then .some (.Val val.get!)
  else .none := rfl

@[simp]
lemma eval_add : Γ st ⟦@Add α x y⟧ₑ = .some (.Val ((st.felts x).get! + (st.felts y).get!)) := rfl

@[simp]
lemma eval_sub : Γ st ⟦@Sub α x y⟧ₑ = .some (.Val ((st.felts x).get! - (st.felts y).get!)) := rfl

@[simp]
lemma eval_mul : Γ st ⟦@Mul α x y⟧ₑ = .some (.Val ((st.felts x).get! * (st.felts y).get!)) := rfl

@[simp]
lemma eval_isz : Γ st ⟦??₀x⟧ₑ = .some (.Val (if (st.felts x).get! = 0 then 1 else 0)) := rfl

@[simp]
lemma eval_inv : Γ st ⟦Inv x⟧ₑ = .some (.Val (if st.felts[x].get! = 0 then 0 else st.felts[x].get!⁻¹)) := rfl

@[simp]
lemma eval_andEqz : Γ st ⟦@AndEqz α c x⟧ₑ =
                    .some (.Constraint ((st.props c).get! ∧ (st.felts x).get! = 0)) := rfl

@[simp]
lemma eval_bitAnd :
  Γ st ⟦@BitAnd α x y⟧ₑ =
    (.some <| .Val <| feltBitAnd (st.felts x).get! (st.felts y).get!) := rfl

@[simp]
lemma eval_neg : Γ st ⟦@Neg α x⟧ₑ = .some (.Val (0 - (st.felts x).get!)) := rfl

@[simp]
lemma eval_pow : Γ st ⟦@Pow α x n⟧ₑ = .some (.Val ((st.felts x).get! ^ n)) := rfl

@[simp]
lemma eval_andCond :
  Γ st ⟦@AndCond α old cnd inner⟧ₑ =
    .some (.Constraint ((st.props old).get! ∧
                       if (st.felts cnd).get! = 0
                       then _root_.True
                       else (st.props inner).get!)) := rfl

end Risc0.Op
