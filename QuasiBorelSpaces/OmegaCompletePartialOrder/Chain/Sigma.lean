module

import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Sigma.Order
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.OmegaCompletePartialOrder

@[expose] public section

namespace OmegaCompletePartialOrder.Chain.Sigma

variable {I : Type*} {P : I → Type*} [∀ i, Preorder (P i)]

/-- Injects a chain into a chain of coproducts. -/
def inj {i} (c : Chain (P i)) : Chain ((i : I) × P i) where
  toFun n := ⟨i, c n⟩
  monotone' n₁ n₂ hn := by
    simp only [Sigma.mk_le_mk_iff]
    apply c.monotone' hn

@[simp]
lemma inj_coe {i} (c : Chain (P i)) (n : ℕ) : inj c n = ⟨i, c n⟩ := rfl

private lemma cast_mono {i j : I} (h : i = j) : Monotone (cast (congr_arg P h)) := by
  intro _ _ h'
  subst h
  exact h'

/-- Converts a chain of coproducts into a coproduct of chains. -/
def distrib (c : Chain ((i : I) × P i)) : (i : I) × Chain (P i) where
  fst := (c 0).fst
  snd := {
    toFun n :=
      have : (c 0).fst = (c n).fst := by
        have := c.monotone (zero_le n)
        rw [Sigma.le_def] at this
        exact this.choose
      this ▸ (c n).snd
    monotone' i₁ i₂ hi := by
      have h₀ := c.monotone (zero_le i₂)
      have h₁ := c.monotone hi
      simp only [Sigma.le_def, eqRec_eq_cast] at h₀ h₁
      simpa only [eqRec_eq_cast, ge_iff_le, cast_cast]
        using cast_mono h₀.fst.symm h₁.snd
  }

@[simp]
lemma distrib_inj {i} (c : Chain (P i)) : distrib (inj c) = ⟨i, c⟩ := rfl

@[elab_as_elim]
lemma distrib_cases
    {p : Chain ((i : I) × P i) → Prop}
    (mk : ∀ {i} (c : Chain (P i)), p (inj c))
    (c : Chain ((i : I) × P i)) : p c := by
  classical
  suffices this : c = inj (distrib c).snd by
    rw [this]
    apply mk
  ext n : 2
  simp only [distrib, Lean.Elab.WF.paramLet, inj_coe]
  have := c.monotone (zero_le n)
  simp only [Sigma.le_def] at this
  ext : 1
  · exact this.choose.symm
  · simp only [Chain, OrderHom.coe_mk, heq_eqRec_iff_heq, heq_eq_eq]

end OmegaCompletePartialOrder.Chain.Sigma
