import QuasiBorelSpaces.Hom
import QuasiBorelSpaces.OmegaCompletePartialOrder.Basic
import QuasiBorelSpaces.OmegaQuasiBorelSpace
import QuasiBorelSpaces.Prod

/-!
# Exponentials for ω-quasi-borel spaces

This file defines the function space `OmegaQuasiBorelHom X Y` (written
`X →ω𝒒 Y`) of Scott-continuous QBS morphisms. It proves that this space is
itself an ωQBS.
-/

open QuasiBorelSpace
open OmegaQuasiBorelSpace
open OmegaCompletePartialOrder

/--
Exponential objects: functions that are both Scott-Continuous and Measurable (QBS Morphisms)
-/
structure OmegaQuasiBorelHom
    (X Y : Type*)
    [OmegaQuasiBorelSpace X] [OmegaQuasiBorelSpace Y] where
  private toFun : X → Y
  private isHom' : IsHom toFun := by fun_prop
  private ωScottContinuous' : ωScottContinuous toFun := by fun_prop

@[inherit_doc] infixr:25 " →ω𝒒 " => OmegaQuasiBorelHom

namespace OmegaQuasiBorelHom

variable {X Y Z : Type*} [OmegaQuasiBorelSpace X] [OmegaQuasiBorelSpace Y] [OmegaQuasiBorelSpace Z]

instance : FunLike (X →ω𝒒 Y) X Y where
  coe f := (f.1 : X → Y)
  coe_injective' f g h := by
    cases f
    cases g
    simp_all only

/-- A simps projection for function coercion. -/
def Simps.coe (f : X →ω𝒒 Y) : X → Y := f

initialize_simps_projections OmegaQuasiBorelHom (toFun → coe)

@[ext]
lemma ext {f g : X →ω𝒒 Y} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

/--
Copy of a `OmegaQuasiBorelHom` with a new `toFun` equal to the old one.
Useful to fix definitional equalities.
-/
protected def copy (f : X →ω𝒒 Y) (f' : X → Y) (h : f' = ⇑f) : X →ω𝒒 Y where
  toFun := f'
  isHom' := h.symm ▸ f.isHom'
  ωScottContinuous' := h.symm ▸ f.ωScottContinuous'

@[simp]
lemma coe_mk {f : X → Y} (hf₁ : IsHom f) (hf₂ : ωScottContinuous f) : ⇑(mk f hf₁ hf₂) = f := rfl

@[simp]
lemma eta (f : X →ω𝒒 Y) : mk f f.isHom' f.ωScottContinuous' = f := rfl

@[simp]
lemma toFun_eq_coe (f : X →ω𝒒 Y) : toFun f = ⇑f := rfl

@[simp, fun_prop]
lemma isHom_coe (f : X →ω𝒒 Y) : IsHom (f : X → Y) := f.2

@[simp, fun_prop]
lemma ωScottContinuous_coe (f : X →ω𝒒 Y) : ωScottContinuous (f : X → Y) := f.3

@[simp]
lemma monotone_coe (f : X →ω𝒒 Y) : Monotone (f : X → Y) := f.3.monotone

instance : PartialOrder (X →ω𝒒 Y) :=
  PartialOrder.lift DFunLike.coe DFunLike.coe_injective

/-- Converts an ωQBS Hom to a Poset Hom. -/
@[simps, coe]
def toOrderHom (f : X →ω𝒒 Y) : X →o Y where
  toFun := f
  monotone' := f.monotone_coe

/-- Converts a ωQBS Hom to an ωCPO Hom. -/
@[simps, coe]
def toContinuousHom (f : X →ω𝒒 Y) : X →𝒄 Y where
  toFun := f
  monotone' := f.monotone_coe
  map_ωSup' := f.ωScottContinuous_coe.map_ωSup

/-- Converts a ωQBS Hom to a quasi-Borel Hom. -/
@[simps, coe]
def toQuasiBorelHom (f : X →ω𝒒 Y) : X →𝒒 Y where
  toFun := f

/-- The ωCPO structure on the exponential is the pointwise order. -/
@[simps!]
instance : OmegaCompletePartialOrder (X →ω𝒒 Y) :=
  OmegaCompletePartialOrder.lift
    ⟨DFunLike.coe, fun _ _ h ↦ h⟩
    (fun c ↦ {
      toFun := ωSup (c.map ⟨DFunLike.coe, fun _ _ h ↦ h⟩)
      isHom' := by
        simp only [
          ωSup, Chain.isHom_iff, Chain.map_coe, Pi.evalOrderHom_coe, OrderHom.coe_mk,
          Function.comp_apply, Function.eval, isHom_coe, implies_true, isHom_ωSup']
      ωScottContinuous' := by
        let c' : Chain (X →𝒄 Y) := {
          toFun n := (c n).toContinuousHom
          monotone' i j h := c.monotone h
        }
        change ωScottContinuous (DFunLike.coe (ωSup c'))
        apply ContinuousHom.ωScottContinuous
    })
    (fun _ _ h ↦ h)
    (by simp only [OrderHom.coe_mk, coe_mk, implies_true])

/-- The QBS structure on the ωHoms is identical to normal QBS Homs. -/
instance : QuasiBorelSpace (X →ω𝒒 Y) where
  IsVar φ := IsHom (fun x : ℝ × X ↦ φ x.1 x.2)
  isVar_const f := by fun_prop
  isVar_comp hf hφ := by
    rw [← isHom_iff_measurable] at hf
    fun_prop
  isVar_cases' {ix} {φ} hix hφ := by
    rw [← isHom_iff_measurable] at hix
    let ix' := fun (p : ℝ × X) ↦ ix p.1
    have hix' : IsHom ix' := by
      apply isHom_comp (hf := hix)
      exact Prod.isHom_fst
    let branches := fun n (p : ℝ × X) ↦ (φ n p.1) p.2
    apply isHom_cases (ix := ix') (f := branches)
    · exact hix'
    · exact hφ

instance : MeasurableSpace (X →ω𝒒 Y) := toMeasurableSpace

@[local simp]
lemma isHom_def (φ : ℝ → X →ω𝒒 Y) :
    IsHom φ ↔ IsHom (fun x : ℝ × X ↦ φ x.1 x.2) := by
  rw [← isVar_iff_isHom]
  rfl

@[simp]
lemma isHom_eval : IsHom (fun p : (X →ω𝒒 Y) × X ↦ p.1 p.2) := by
  rw [QuasiBorelSpace.isHom_def]
  intro φ hφ
  have h_func : IsHom (fun r ↦ (φ r).1) := isHom_comp Prod.isHom_fst hφ
  have h_arg  : IsHom (fun r ↦ (φ r).2) := isHom_comp Prod.isHom_snd hφ
  rw [isHom_def] at h_func
  have h_input : IsHom (fun r : ℝ ↦ (r, (φ r).2)) := by
    apply Prod.isHom_mk
    · exact isHom_id
    · exact h_arg
  apply isHom_comp (hf := h_func) (hg := h_input)

@[simp]
lemma ωScottContinuous_eval : ωScottContinuous (fun p : (X →ω𝒒 Y) × X ↦ p.1 p.2) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun x y ⟨h₁, h₂⟩ ↦ ?_, fun c ↦ ?_⟩
  · trans
    · apply h₁
    · apply y.1.monotone_coe
      apply h₂
  · simp only [Prod.ωSup_fst, Prod.ωSup_snd, ωSup_coe]
    apply le_antisymm
    · simp only [
        ωSup, ωSup_le_iff, Chain.map_coe, Pi.evalOrderHom_coe, OrderHom.coe_mk,
        Function.comp_apply, Function.eval, OrderHom.fst_coe]
      intro i
      rw [(c i).1.ωScottContinuous_coe.map_ωSup]
      simp only [ωSup_le_iff, Chain.map_coe, OrderHom.coe_mk, Function.comp_apply, OrderHom.snd_coe]
      intro j
      apply le_ωSup_of_le (i ⊔ j)
      simp only [Chain.map_coe, OrderHom.coe_mk, Function.comp_apply]
      trans
      · apply (c.monotone (by grind : i ≤ i ⊔ j)).1
      · apply (c (i ⊔ j)).1.monotone_coe
        apply (c.monotone (by grind : j ≤ i ⊔ j)).2
    · simp only [ωSup_le_iff, Chain.map_coe, OrderHom.coe_mk, Function.comp_apply]
      intro i
      apply le_ωSup_of_le i
      simp only [
        Chain.map_coe, Pi.evalOrderHom_coe, OrderHom.coe_mk,
        Function.comp_apply, Function.eval, OrderHom.fst_coe]
      apply (c i).1.monotone_coe
      apply le_ωSup_of_le i
      simp only [Chain.map_coe, Function.comp_apply, OrderHom.snd_coe, le_refl]

omit [OmegaQuasiBorelSpace X] in
@[fun_prop]
lemma isHom_eval' [QuasiBorelSpace X]
    {f : X → Y →ω𝒒 Z} (hf : IsHom f)
    {g : X → Y} (hg : IsHom g)
    : IsHom (fun x ↦ f x (g x)) := by
  apply isHom_comp' (f := fun x ↦ x.1 x.2) (g := fun x ↦ (f x, g x))
  · simp only [isHom_eval]
  · fun_prop

@[fun_prop]
lemma ωScottContinuous_eval'
    {f : X → Y →ω𝒒 Z} (hf : ωScottContinuous f)
    {g : X → Y} (hg : ωScottContinuous g)
    : ωScottContinuous (fun x ↦ f x (g x)) := by
  apply ωScottContinuous.comp (g := fun x ↦ x.1 x.2) (f := fun x ↦ (f x, g x))
  · simp only [ωScottContinuous_eval]
  · fun_prop

omit [OmegaQuasiBorelSpace X] in
@[simp]
lemma isHom_iff
    [QuasiBorelSpace X] (f : X → Y →ω𝒒 Z)
    : IsHom f ↔ IsHom (fun x : X × Y ↦ f x.1 x.2) := by
  apply Iff.intro
  · intro hf
    rw [QuasiBorelSpace.isHom_def]
    simp only [Prod.isHom_iff, and_imp]
    intro φ hφ₁ hφ₂
    fun_prop
  · intro hf
    rw [QuasiBorelSpace.isHom_def]
    intro φ hφ
    simp only [isHom_def]
    fun_prop

@[fun_prop]
lemma isHom_mk
    {f : X → Y → Z}
    (h₁ : IsHom fun x : X × Y ↦ f x.1 x.2)
    (h₂ : ∀x, ωScottContinuous (f x))
    : IsHom fun x ↦ mk (f x) (by fun_prop) (h₂ x) := by
  simp only [isHom_iff, coe_mk, h₁]

@[fun_prop]
lemma ωScottContinuous_mk
    {f : X → Y → Z}
    (h₁ : ∀ x, IsHom (f x))
    (h₂ : ωScottContinuous fun x : X × Y ↦ f x.1 x.2)
    : ωScottContinuous fun x ↦ mk (f x) (h₁ x) (by fun_prop) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun x y h z ↦ ?_, fun c ↦ ?_⟩
  · have : (x, z) ≤ (y, z) := ⟨h, le_rfl⟩
    exact h₂.monotone this
  · ext x
    simp only [coe_mk, ωSup]
    rw [(by simp only [ωSup_const] : x = ωSup (Chain.const x))]
    change f (ωSup (Chain.zip c (Chain.const x))).1 (ωSup (Chain.zip c (Chain.const x))).2 = _
    rw [h₂.map_ωSup]
    congr 1
    ext n
    simp only [
      Chain.map_coe, OrderHom.coe_mk, Function.comp_apply, Chain.zip_coe,
      Chain.const_apply, ωSup_const, Pi.evalOrderHom_coe, Function.eval, coe_mk]

/-- The exponential object is an ωQBS. -/
instance : OmegaQuasiBorelSpace (X →ω𝒒 Y) where
  isHom_ωSup := by
    simp only [ωSup, isHom_iff, coe_mk]
    apply isHom_ωSup'
    simp only [
      Chain.isHom_iff, Chain.map_coe, Pi.evalOrderHom_coe,
      OrderHom.coe_mk, Function.comp_apply, Function.eval]
    intro i
    apply isHom_comp'
        (f := fun x : (X →ω𝒒 Y) × X ↦ x.1 x.2)
        (g := fun x : Chain (X →ω𝒒 Y) × X ↦ (x.1 i, x.2))
    · fun_prop
    · apply Prod.isHom_mk
      · apply isHom_comp' (Chain.isHom_apply i) Prod.isHom_fst
      · fun_prop

/-! ### Operations -/

/-- Identity `OmegaQuasiBorelHom`s. -/
@[simps]
def id : X →ω𝒒 X where
  toFun x := x

/-- Function composition for `OmegaQuasiBorelHom`s. -/
@[simps coe]
def comp (f : Y →ω𝒒 Z) (g : X →ω𝒒 Y) : X →ω𝒒 Z where
  toFun x := f (g x)

/-- Product construction as an `OmegaQuasiBorelHom`. -/
@[simps coe]
def Prod.mk (f : X →ω𝒒 Y) (g : X →ω𝒒 Z) : X →ω𝒒 Y × Z where
  toFun x := (f x, g x)

/-- First product projection. -/
@[simps coe]
def Prod.fst : X × Y →ω𝒒 X where
  toFun x := x.1

/-- Second product projection. -/
@[simps coe]
def Prod.snd : X × Y →ω𝒒 Y where
  toFun x := x.2

/-- Currying for `OmegaQuasiBorelHom`s. -/
@[simps coe]
def curry (f : Z × X →ω𝒒 Y) : Z →ω𝒒 (X →ω𝒒 Y) where
  toFun x := { toFun y := f (x, y) }

/-- Function application is an `OmegaQuasiBorelHom`. -/
@[simps coe]
def eval : (X →ω𝒒 Y) × X →ω𝒒 Y where
  toFun x := x.1 x.2

/-- Uncurrying for `OmegaQuasiBorelHom`s. -/
@[simps!]
def uncurry (f : X →ω𝒒 Y →ω𝒒 Z) : X × Y →ω𝒒 Z :=
  eval.comp (Prod.mk (comp f Prod.fst) Prod.snd)

@[simp]
lemma curry_uncurry (f : Z →ω𝒒 (X →ω𝒒 Y)) : curry (uncurry f) = f := rfl

@[simp]
lemma uncurry_curry (f : Z × X →ω𝒒 Y) : uncurry (curry f) = f := rfl

end OmegaQuasiBorelHom
