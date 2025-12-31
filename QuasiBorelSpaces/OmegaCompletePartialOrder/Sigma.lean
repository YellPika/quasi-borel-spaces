import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Data.Sigma.Order

namespace OmegaCompletePartialOrder.Sigma

variable {I : Type*} {P : I → Type*}

@[local simp]
private lemma chain_eq
    [∀ i, Preorder (P i)]
    (c : Chain ((i : I) × P i)) (n : ℕ)
    : (c n).fst = (c 0).fst := by
  have : c 0 ≤ c n := c.monotone (by simp only [Nat.zero_le])
  simp only [Sigma.le_def] at this
  rcases this with ⟨h₁, h₂⟩
  rw [h₁]

private lemma cast_le
    [∀ i, LE (P i)] {i j} (h : j = i) {x : P i} {y : P j} (h' : h ▸ x ≤ y)
    : x ≤ cast (congr_arg P h) y := by
  cases h
  simp_all only [cast_eq]

private lemma le_cast
    [∀ i, LE (P i)] {i j} (h : i = j) {x : P i} {y : P j} (h' : x ≤ h ▸ y)
    : cast (congr_arg P h) x ≤ y := by
  cases h
  simp_all only [cast_eq]

instance [∀ i, OmegaCompletePartialOrder (P i)] : OmegaCompletePartialOrder ((i : I) × P i) where
  ωSup c := {
    fst := (c 0).fst
    snd := ωSup {
      toFun n := Eq.mp (by simp only [chain_eq]) (c n).snd
      monotone' i j h := by
        simp only [eq_mp_eq_cast]
        have : c i ≤ c j := c.monotone h
        simp only [Sigma.le_def] at this
        rcases this with ⟨h₁, h₂⟩
        apply cast_le
        · simp only [eqRec_eq_cast, cast_cast] at ⊢ h₂
          exact h₂
        · simp only [chain_eq]
    }
  }
  le_ωSup c i := by
    simp only [eq_mp_eq_cast, ge_iff_le, Sigma.le_def, chain_eq, exists_true_left]
    apply le_ωSup_of_le i
    simp only [Chain, eqRec_eq_cast, OrderHom.coe_mk, le_refl]
  ωSup_le := by
    rintro c ⟨x, y⟩ h
    simp only [eq_mp_eq_cast, ge_iff_le, Sigma.le_def]
    have := h 0
    simp only [Sigma.le_def] at this
    rcases this with ⟨this, _⟩
    simp only [eqRec_eq_cast, this, exists_true_left, ge_iff_le]
    apply le_cast this
    apply ωSup_le
    intro i
    simp only [Chain, OrderHom.coe_mk, eqRec_eq_cast]
    have := h i
    simp only [Sigma.le_def] at this
    rcases this with ⟨h₁, h₂⟩
    apply cast_le
    · simp only [eqRec_eq_cast, cast_cast] at ⊢ h₂
      exact h₂
    · simp only [chain_eq] at h₁
      simp only [h₁]

lemma fst_ωSup
    [∀ i, OmegaCompletePartialOrder (P i)] (c : Chain ((i : I) × P i)) (n : ℕ)
    : (ωSup c).fst = (c n).fst := by
  simp only [ωSup, eq_mp_eq_cast, chain_eq]

end OmegaCompletePartialOrder.Sigma
