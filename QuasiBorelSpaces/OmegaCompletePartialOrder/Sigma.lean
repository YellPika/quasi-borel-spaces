module

public import Mathlib.Data.Sigma.Order
public import Mathlib.Order.OmegaCompletePartialOrder
public import QuasiBorelSpaces.OmegaCompletePartialOrder.Chain.Sigma

public section

namespace OmegaCompletePartialOrder.Sigma

variable {I : Type*} {P : I → Type*} [∀ i, OmegaCompletePartialOrder (P i)]

instance : OmegaCompletePartialOrder ((i : I) × P i) where
  ωSup c := (Chain.Sigma.distrib c).map id fun _ ↦ ωSup
  le_ωSup c i := by
    simp only [ge_iff_le]
    cases c using Chain.Sigma.distrib_cases with
    | mk c =>
      simp only [
        Chain.Sigma.inj_coe, id_eq, Chain.Sigma.distrib_inj,
        Sigma.map_mk, Sigma.mk_le_mk_iff]
      apply le_ωSup
  ωSup_le := by
    rintro c ⟨x, y⟩ h
    simp only [ge_iff_le]
    cases c using Chain.Sigma.distrib_cases with
    | mk c =>
      simp only [Chain.Sigma.inj_coe, ge_iff_le, Sigma.le_def] at h
      have h' := (h 0).choose
      subst h'
      simp only [
        exists_const, id_eq, Chain.Sigma.distrib_inj, Sigma.map_mk,
        Sigma.mk_le_mk_iff, ωSup_le_iff] at ⊢ h
      exact h

@[simp]
lemma ωSup_inj {i} (c : Chain (P i)) : ωSup (Chain.Sigma.inj c) = ⟨i, ωSup c⟩ := rfl

end OmegaCompletePartialOrder.Sigma
