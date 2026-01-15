module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Sigma.Order
public import Mathlib.Order.OmegaCompletePartialOrder
public import Mathlib.Tactic.Have

@[expose] public section

namespace OmegaCompletePartialOrder.Chain.Sigma

variable {I : Type*} {P : I → Type*}

private lemma cast_le
    [∀ i, LE (P i)] {i j} (h : j = i) {x : P i} {y : P j} (h' : h ▸ x ≤ y)
    : x ≤ cast (congr_arg P h) y := by
  cases h
  simp_all only [cast_eq]

variable [∀ i, Preorder (P i)]

/-- Injects a chain into a chain of coproducts. -/
def inj {i} (c : Chain (P i)) : Chain ((i : I) × P i) where
  toFun n := ⟨i, c n⟩
  monotone' n₁ n₂ hn := by
    simp only [Sigma.mk_le_mk_iff]
    apply c.monotone' hn

@[simp]
lemma inj_coe {i} (c : Chain (P i)) (n : ℕ) : inj c n = ⟨i, c n⟩ := rfl

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
      simp only [eqRec_eq_cast]
      apply cast_le
      · simp only [eqRec_eq_cast, cast_cast]
        have := c.monotone hi
        simp only [Sigma.le_def, eqRec_eq_cast] at this
        exact this.choose_spec
      · have := c.monotone (zero_le i₂)
        rw [Sigma.le_def] at this
        exact this.choose.symm
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
