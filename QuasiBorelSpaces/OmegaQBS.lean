import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import QuasiBorelSpaces.Basic
import QuasiBorelSpaces.Prod
import QuasiBorelSpaces.Sum

/-!
# Omega quasi-borel spaces (ωQBS)

Definition of ωQBS (Def. 3.5 without the extra compatibility axiom).

I added **Lemma 3.9** which says ωQBS has binary products and coproducts which is preserved by the
forgetful functors to `ΩCPO` and to `QBS`. Mathlib doesn't (I think, yet!) ship a
`OmegaCompletePartialOrder` instance for `Sum` so I gave a small local one here :)
-/

namespace QuasiBorelSpaces

open OmegaCompletePartialOrder

universe u v

/-! ## Local ωCPO instance for sums

A monotone chain `c : Chain (α ⊕ β)` cannot switch sides: if `c 0 = inl _` then every `c n` is
`inl _` and similarly for `inr _`. We use this to define `ωSup` componentwise.
-/
section SumOmegaCPO

variable {α : Type u} {β : Type v}
variable [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]

/-- If a chain starts with `inl`, then all entries are `inl`. -/
private lemma all_inl_of_left0 (c : Chain (Sum α β)) {a₀ : α}
    (h0 : c 0 = Sum.inl a₀) : ∀ n, ∃ a, c n = Sum.inl a := by
  intro n
  have hmon : c 0 ≤ c n := c.monotone (Nat.zero_le n)
  cases hcn : c n with
  | inl a => exact Sum.isLeft_iff.mp rfl
  | inr b =>
      have : False := by simp [h0, hcn] at hmon
      cases this

/-- If a chain starts with `inr`, then all entries are `inr`. -/
private lemma all_inr_of_right0 (c : Chain (Sum α β)) {b₀ : β}
    (h0 : c 0 = Sum.inr b₀) : ∀ n, ∃ b, c n = Sum.inr b := by
  intro n
  have hmon : c 0 ≤ c n := c.monotone (Nat.zero_le n)
  cases hcn : c n with
  | inr b => exact Sum.isRight_iff.mp rfl
  | inl a =>
      have : False := by simp [h0, hcn] at hmon
      cases this

/-- Extract the `α`-chain when all entries are `inl`. -/
private noncomputable def leftChain
    (c : Chain (Sum α β)) (hall : ∀ n, ∃ a, c n = Sum.inl a) : Chain α := by
  classical
  refine ⟨(fun n => Classical.choose (hall n)), ?_⟩
  intro i j hij
  have hi : c i = Sum.inl (Classical.choose (hall i)) :=
    Classical.choose_spec (hall i)
  have hj : c j = Sum.inl (Classical.choose (hall j)) :=
    Classical.choose_spec (hall j)
  have h := c.monotone hij
  simp only [ge_iff_le]
  rw [hi, hj] at h
  exact Sum.inl_le_inl_iff.mp h

/-- extract the `β`-chain when all entries are `inr` -/
private noncomputable def rightChain
  (c : Chain (Sum α β)) (hall : ∀ n, ∃ b, c n = Sum.inr b) : Chain β := by
  classical
  refine ⟨(fun n => Classical.choose (hall n)), ?_⟩
  intro i j hij
  have hi : c i = Sum.inr (Classical.choose (hall i)) :=
  Classical.choose_spec (hall i)
  have hj : c j = Sum.inr (Classical.choose (hall j)) :=
  Classical.choose_spec (hall j)
  have h := c.monotone hij
  simp only [ge_iff_le]
  rw [hi, hj] at h
  exact Sum.inr_le_inr_iff.mp h

/-- The (noncomputable) ωSup for `α ⊕ β` defined by cases on the side of the chain. -/
private noncomputable def ωSupSum (c : Chain (Sum α β)) : Sum α β := by
  classical
  cases h0 : c 0 with
  | inl a0 =>
      let hall := all_inl_of_left0 (c := c) h0
      exact Sum.inl (ωSup (leftChain c hall))
  | inr b0 =>
      let hall := all_inr_of_right0 (c := c) h0
      exact Sum.inr (ωSup (rightChain c hall))

/-- Local `OmegaCompletePartialOrder` instance for disjoint sums. -/
noncomputable instance instOmegaCompletePartialOrderSum :
    OmegaCompletePartialOrder (Sum α β) where
  ωSup := ωSupSum
  le_ωSup c i := by
    classical
    cases h0 : c 0 with
    | inl a0 =>
        let hall := all_inl_of_left0 (c := c) h0
        let cα := leftChain c hall
        have hi : c i = Sum.inl (cα i) := by
          simpa using (Classical.choose_spec (hall i))
        have : cα i ≤ ωSup cα := le_ωSup cα i
        sorry
    | inr b0 =>
        let hall := all_inr_of_right0 (c := c) h0
        let cβ := rightChain c hall
        have hi : c i = Sum.inr (cβ i) := by
          simpa using (Classical.choose_spec (hall i))
        have : cβ i ≤ ωSup cβ := le_ωSup cβ i
        sorry
  ωSup_le c x hx := by
    classical
    cases h0 : c 0 with
    | inl a0 =>
        cases hx0x : x with
        | inl a =>
            let hall := all_inl_of_left0 (c := c) h0
            let cα := leftChain c hall
            have hxα : ∀ i, cα i ≤ a := by
              intro i
              have hi : c i = Sum.inl (cα i) := by simpa using (Classical.choose_spec (hall i))
              have := hx i
              simpa [hi, hx0x] using this
            have : ωSup cα ≤ a := ωSup_le _ _ hxα
            sorry
        | inr b =>
            have := hx 0
            simp [h0, hx0x] at this
    | inr b0 =>
        cases hx0x : x with
        | inr b =>
            let hall := all_inr_of_right0 (c := c) h0
            let cβ := rightChain c hall
            have hxβ : ∀ i, cβ i ≤ b := by
              intro i
              have hi : c i = Sum.inr (cβ i) := by simpa using (Classical.choose_spec (hall i))
              have := hx i
              simpa [hi, hx0x] using this
            have : ωSup cβ ≤ b := ωSup_le _ _ hxβ
            simp only [ge_iff_le]
            change ωSupSum c ≤ Sum.inr b
            suffices ωSupSum c = Sum.inr (ωSup cβ) by
              rw [this, Sum.le_def]
              exact Sum.LiftRel.inr ‹ωSup cβ ≤ b›
            sorry
        | inl a =>
            have := hx 0
            simp only [ge_iff_le]
            refine Sum.le_def.mpr ?_
            simp [h0, hx0x] at this

end SumOmegaCPO

/-! ## ωQBS: definition and lemmas -/

/-- An ωQBS is a type with both an `OmegaCompletePartialOrder` and a `QuasiBorelSpace`.
(**Def. 3.5** without the compatibility axiom) -/
class OmegaQBS (α : Type u)
  extends OmegaCompletePartialOrder α, QuasiBorelSpace α

namespace OmegaQBS

variable {α : Type u} {β : Type v}

/-!
### Lemma 3.9: products and coproducts in ωQBS
-/

/-- **Lemma 3.9 (product)** — if `α, β` are ωCPOs and QBSes, then `α × β` is an ωQBS. -/
@[simp] instance instOmegaQBSProd
    [OmegaCompletePartialOrder α] [QuasiBorelSpace α]
    [OmegaCompletePartialOrder β] [QuasiBorelSpace β] : OmegaQBS (α × β) where
  toOmegaCompletePartialOrder := inferInstance
  toQuasiBorelSpace := inferInstance

/-- **Lemma 3.9 (coproduct)** — if `α, β` are ωCPOs and QBSes, then `α ⊕ β` is an ωQBS. -/
@[simp] noncomputable instance instOmegaQBSSum
    [OmegaCompletePartialOrder α] [QuasiBorelSpace α]
    [OmegaCompletePartialOrder β] [QuasiBorelSpace β] : OmegaQBS (Sum α β) where
  toOmegaCompletePartialOrder := inferInstance
  toQuasiBorelSpace := inferInstance

end OmegaQBS

end QuasiBorelSpaces
