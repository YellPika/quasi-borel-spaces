import QuasiBorelSpaces.Prod
import QuasiBorelSpaces.OmegaQuasiBorelSpace

/-!
# Small Products of Quasi-Borel Spaces

This file defines small products of quasi-borel spaces by giving a
`QuasiBorelSpace` instance for the `· → ·` type.

See [HeunenKSY17], Proposition 16.
-/

namespace QuasiBorelSpace.Pi

variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]
  {C : Type*} [QuasiBorelSpace C]
  {I : Type*} {P : I → Type*} [∀ i, QuasiBorelSpace (P i)]

instance : QuasiBorelSpace (∀i : I, P i) where
  IsVar φ := ∀ i, IsHom (φ · i)
  isVar_const f i := by simp only [isHom_const]
  isVar_comp hf hφ i := by
    rw [←isHom_iff_measurable] at hf
    fun_prop
  isVar_cases' hix hφ i :=
    isHom_cases (by simp only [isHom_ofMeasurableSpace, hix]) (hφ · i)

@[local simp]
lemma isHom_def (φ : ℝ → ∀ i, P i) : IsHom φ ↔ ∀ i, IsHom (φ · i) := by
  rw [←isVar_iff_isHom]
  rfl

@[fun_prop]
lemma isHom_apply (i : I) : IsHom (fun (f : (i : I) → P i) ↦ f i) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def]
  fun_prop

@[fun_prop]
lemma isHom_pi {f : A → ∀ i, P i} (hf : ∀ i, IsHom (f · i)) : IsHom f := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def]
  fun_prop

@[simp]
lemma isHom_iff {f : A → (i : I) → P i} : IsHom f ↔ ∀i, IsHom (f · i) := by
  apply Iff.intro
  · fun_prop
  · exact isHom_pi

instance
    [∀ i, MeasurableSpace (P i)]
    [∀ i, MeasurableQuasiBorelSpace (P i)]
    : MeasurableQuasiBorelSpace (∀i, P i) where
  isHom_iff_measurable φ := by
    apply Iff.intro <;>
    · simp only [isHom_iff, isHom_iff_measurable]
      fun_prop

end QuasiBorelSpace.Pi

namespace OmegaQuasiBorelSpace.Pi

open QuasiBorelSpace
open OmegaCompletePartialOrder

variable {I : Type*} {P : I → Type*} [∀ i, OmegaQuasiBorelSpace (P i)]

instance : OmegaQuasiBorelSpace (∀i, P i) where
  isHom_ωSup' c hc := by
    rw [Pi.isHom_iff]
    intro i
    let c' := c.map ⟨(fun f r ↦ f r i), by intro f g h r; exact h r i⟩
    apply isHom_ωSup c' fun n ↦ ?_
    simp only [Chain.map_coe, OrderHom.coe_mk, Function.comp_apply, c']
    fun_prop

end OmegaQuasiBorelSpace.Pi

namespace QuasiBorelSpace.Chain

open OmegaCompletePartialOrder

variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]
  {C : Type*} [QuasiBorelSpace C]

instance [Preorder A] : QuasiBorelSpace (Chain A) :=
  .lift fun f ↦ (f : ℕ → A)


@[local simp]
lemma isHom_def [Preorder A] (φ : ℝ → Chain A) : IsHom φ ↔ ∀ i, IsHom (φ · i) := by
  rw [←isVar_iff_isHom]
  rfl

@[fun_prop]
lemma isHom_apply [Preorder A] (i : ℕ) : IsHom (fun (f : Chain A) ↦ f i) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def]
  fun_prop

@[fun_prop]
lemma isHom_pi [Preorder B] {f : A → Chain B} (hf : ∀ i, IsHom (f · i)) : IsHom f := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def]
  fun_prop

@[simp]
lemma isHom_iff [Preorder B] {f : A → Chain B} : IsHom f ↔ ∀i, IsHom (f · i) := by
  apply Iff.intro
  · intro hf i
    apply isHom_comp' (isHom_apply i) hf
  · exact isHom_pi

end QuasiBorelSpace.Chain

namespace OmegaQuasiBorelSpace

open QuasiBorelSpace
open OmegaCompletePartialOrder

variable {A : Type*} [OmegaQuasiBorelSpace A]

@[fun_prop, simp]
lemma isHom_ωSup'' : IsHom (ωSup : Chain A → A) := by
  rw [isHom_def]
  intro φ hφ
  let φ' : Chain (ℝ → A) :=
    { toFun n r := φ r n
    , monotone' n₁ n₂  hn r := (φ r).monotone hn
    }
  change IsHom (ωSup φ')
  simp only [Chain.isHom_iff] at hφ
  apply isHom_ωSup φ' hφ

end OmegaQuasiBorelSpace
