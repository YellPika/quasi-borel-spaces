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
    cases c using Chain.Sigma.distrib_cases
    simp only [
      Chain.Sigma.inj_coe, id_eq, Chain.Sigma.distrib_inj,
      Sigma.map_mk, Sigma.mk_le_mk_iff, le_ωSup]
  ωSup_le := by
    rintro c ⟨x, y⟩ h
    cases c using Chain.Sigma.distrib_cases
    simp only [Chain.Sigma.inj_coe, ge_iff_le] at h
    cases h 0
    simp only [Sigma.mk_le_mk_iff] at h
    simp only [
      Sigma.map, id_eq, Chain.Sigma.distrib_inj,
      Sigma.mk_le_mk_iff, ωSup_le_iff, h, implies_true]

@[simp]
lemma ωSup_inj {i} (c : Chain (P i)) : ωSup (Chain.Sigma.inj c) = ⟨i, ωSup c⟩ := rfl

end OmegaCompletePartialOrder.Sigma
