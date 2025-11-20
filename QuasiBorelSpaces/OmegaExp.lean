import QuasiBorelSpaces.Hom
import QuasiBorelSpaces.OmegaCompletePartialOrder.Basic
import QuasiBorelSpaces.OmegaCompletePartialOrder.Limit
import QuasiBorelSpaces.OmegaQuasiBorelSpace
import QuasiBorelSpaces.Prod

/-!
# Exponentials for ω-quasi-borel spaces

This file defines the function space `OmegaHom X Y` (written `X →ω𝒒 Y`) of
Scott-continuous QBS morphisms. It proves that this space is itself an ωQBS.
-/

namespace QuasiBorelSpaces

open QuasiBorelSpace
open OmegaCompletePartialOrder

universe u v w

/--
pointwise supremum of a chain of QBS morphisms is a QBS morphism
(also known as the "Compatibility Axiom" for the exponential to be an ωQBS)
-/
lemma isHom_ωSup_of_chain
    {X : Type u} {Y : Type v}
    [QuasiBorelSpace X] [OmegaQuasiBorelSpace Y]
    (c : Chain (X → Y)) (hc : ∀ n, IsHom (c n)) :
    IsHom (ωSup c) := by
  rw [QuasiBorelSpace.isHom_def]
  intro α hα
  let comp : (X → Y) →o (ℝ → Y) :=
    { toFun := fun f r => f (α r)
      monotone' := by intro f g h r; exact h (α r) }
  let c' : Chain (ℝ → Y) := c.map comp
  have hc' : ∀ n, IsHom (c' n) := by
    intro n
    exact isHom_comp (hf := hc n) (hg := hα)
  have hSup := (OmegaQuasiBorelSpace.isHom_ωSup (α := Y) c' hc')
  have h_eval : ωSup c' = fun r => ωSup c (α r) := by
    funext r
    have hω := OmegaCompletePartialOrder.ωSup_eval (c := c') (x := r)
    have hchain : c'.map (evalOrderHom r) = c.map (evalOrderHom (α r)) := by ext n; rfl
    simpa [hchain] using hω
  simpa [h_eval] using hSup

/--
the type of the Exponential Object:
Functions that are both Scott-Continuous and Measurable (QBS Morphisms)
-/
def OmegaHom (X : Type u) (Y : Type v)
    [OmegaQuasiBorelSpace X] [OmegaQuasiBorelSpace Y] :=
  { f : X →𝒄 Y // IsHom (f : X → Y) }

@[inherit_doc] infixr:25 " →ω𝒒 " => OmegaHom

namespace OmegaHom

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [OmegaQuasiBorelSpace X] [OmegaQuasiBorelSpace Y] [OmegaQuasiBorelSpace Z]

instance : FunLike (X →ω𝒒 Y) X Y where
  coe f := (f.1 : X → Y)
  coe_injective' f g h := by
    apply Subtype.ext
    apply ContinuousHom.ext
    intro x
    exact congrArg (fun k => k x) h

@[ext]
lemma ext {f g : X →ω𝒒 Y} (h : ∀ x, f x = g x) : f = g := by
  apply Subtype.ext
  apply ContinuousHom.ext
  intro x
  exact h x

@[simp, fun_prop]
lemma isHom_coe (f : X →ω𝒒 Y) : IsHom (f : X → Y) := f.2

@[simp]
lemma monotone (f : X →ω𝒒 Y) : Monotone f := (f.1).monotone

/-- the ωCPO structure on the exponential is the pointwise order -/
instance : OmegaCompletePartialOrder (X →ω𝒒 Y) :=
  OmegaCompletePartialOrder.subtype
    (p := fun f : X →𝒄 Y => IsHom (f : X → Y))
    (hp := by
      intro c hc
      have hc_hom : ∀ n, IsHom (c n : X → Y) := by
        intro n
        exact hc (c n) ⟨n, rfl⟩
      let c_raw : Chain (X → Y) :=
        ⟨fun n x => c n x, by intro i j h x; exact c.monotone h x⟩
      have hSup := isHom_ωSup_of_chain c_raw hc_hom
      have h_eq : (ωSup c_raw : X → Y) = (ωSup c : X →𝒄 Y) := by
        funext x
        trans ωSup ((c.map ContinuousHom.toMono).map (OrderHom.apply x))
        · apply OmegaCompletePartialOrder.ωSup_eval
        · rfl
      rw [h_eq] at hSup
      exact hSup)

/-- the QBS structure on the exponential (the standard Function Space definition) -/
instance : QuasiBorelSpace (X →ω𝒒 Y) where
  IsVar φ := IsHom (fun x : ℝ × X ↦ φ x.1 x.2)
  isVar_const f := by fun_prop
  isVar_comp hf hφ := by
    rw [← isHom_iff_measurable] at hf
    fun_prop
  isVar_cases' {ix} {φ} hix hφ := by
    rw [← isHom_iff_measurable] at hix
    let ix' := fun (p : ℝ × X) => ix p.1
    have hix' : IsHom ix' := by
      apply isHom_comp (hf := hix)
      exact Prod.isHom_fst
    let branches := fun n (p : ℝ × X) => (φ n p.1) p.2
    apply isHom_cases (ix := ix') (f := branches)
    · exact hix'
    · exact hφ

/-- uncurried random variables correspond to morphisms -/
@[local simp]
lemma isHom_def (φ : ℝ → X →ω𝒒 Y) :
    IsHom φ ↔ IsHom (fun x : ℝ × X => φ x.1 x.2) := by
  rw [← isVar_iff_isHom]
  rfl

@[simp, fun_prop]
lemma isHom_eval : IsHom (fun p : (X →ω𝒒 Y) × X => p.1 p.2) := by
  rw [QuasiBorelSpace.isHom_def]
  intro φ hφ
  have h_func : IsHom (fun r => (φ r).1) := isHom_comp Prod.isHom_fst hφ
  have h_arg  : IsHom (fun r => (φ r).2) := isHom_comp Prod.isHom_snd hφ
  rw [isHom_def] at h_func
  have h_input : IsHom (fun r : ℝ => (r, (φ r).2)) := by
    apply Prod.isHom_mk
    · exact isHom_id
    · exact h_arg
  apply isHom_comp (hf := h_func) (hg := h_input)

/-! ### OmegaQuasiBorelSpace Instance -/

/--
the exponential object is an ωQBS, we must show that the ω-supremum operation is measurable
-/
instance : OmegaQuasiBorelSpace (X →ω𝒒 Y) where
  isHom_ωSup := by
    intro c hc
    rw [isHom_def]
    let c_uncurry : Chain ((ℝ × X) → Y) := {
      toFun := fun n p => (c n p.1) p.2
      monotone' := by
        intro i j h p
        exact (c.monotone h p.1) p.2
    }
    have hc_uncurry : ∀ n, IsHom (c_uncurry n) := by
      intro n
      specialize hc n
      rw [isHom_def] at hc
      exact hc
    have hSup := isHom_ωSup_of_chain c_uncurry hc_uncurry
    have eq : (fun p => (ωSup c p.1) p.2) = ωSup c_uncurry := by
      ext p
      simp only [c_uncurry]
      rw [OmegaCompletePartialOrder.ωSup_eval]
      rfl
    rw [eq]
    exact hSup

/-! ### Currying Operations -/

/--
currying map: `(Z × X → Y) → (Z → (X → Y))`
constructed using explicit `ContinuousHom` records to match fields `monotone'` and `map_ωSup'`.
-/
def curry (f : Z × X →ω𝒒 Y) : Z →ω𝒒 (X →ω𝒒 Y) :=
  ⟨{
    toFun := fun z => ⟨{
      toFun := fun x => f (z, x)
      monotone' := by
        intro x1 x2 h
        exact f.monotone ⟨le_rfl, h⟩
      map_ωSup' := by
        intro c
        let c_prod : Chain (Z × X) := {
          toFun := fun n => (z, c n),
          monotone' := fun i j h => ⟨le_rfl, c.monotone h⟩
        }
        have hf := f.1.map_ωSup' c_prod
        convert hf
        change z = ωSup (c_prod.map OrderHom.fst)
        have : c_prod.map OrderHom.fst = Chain.const z := rfl
        rw [this, OmegaCompletePartialOrder.ωSup_const]
    }, by
      apply isHom_comp (hf := f.2)
      apply Prod.isHom_mk
      · apply isHom_const
      · apply isHom_id
    ⟩
    monotone' := by
      intro z1 z2 h x
      exact f.monotone ⟨h, le_rfl⟩
    map_ωSup' := by
      intro c
      apply OmegaHom.ext; intro x
      dsimp
      change f.1 (ωSup c, x) = _
      let c_prod : Chain (Z × X) := {
        toFun := fun n => (c n, x),
        monotone' := fun i j h => ⟨c.monotone h, le_refl x⟩
      }
      have h := f.1.map_ωSup' c_prod
      have h_lhs : f.1 (ωSup c, x) = f.1 (ωSup c_prod) := by
        congr 1
        apply Prod.ext
        · rw [Prod.ωSup_fst]; rfl
        · rw [Prod.ωSup_snd]
          have : c_prod.map OrderHom.snd = Chain.const x := rfl
          rw [this, OmegaCompletePartialOrder.ωSup_const]
      rw [h_lhs]
      exact h
  }, by
    rw [QuasiBorelSpace.isHom_def]
    intro φ hφ
    rw [isHom_def]
    dsimp
    apply isHom_comp (hf := f.2)
    apply Prod.isHom_mk
    · apply isHom_comp (hf := hφ) (hg := Prod.isHom_fst)
    · exact Prod.isHom_snd
  ⟩

/-- uncurrying map: `(Z → (X → Y)) → (Z × X → Y)` -/
def uncurry (f : Z →ω𝒒 (X →ω𝒒 Y)) : Z × X →ω𝒒 Y :=
  ⟨{
    toFun := fun p => f p.1 p.2
    monotone' := by
      intro p1 p2 h
      apply le_trans (f.monotone h.1 p1.2)
      apply (f p2.1).monotone h.2
    map_ωSup' := by
      intro c
      let c1 := c.map OrderHom.fst
      let c2 := c.map OrderHom.snd
      let chain_inner (n : ℕ) : Chain Y := {
        toFun := fun m => f (c1 n) (c2 m)
        monotone' := by
          intro i j h
          apply (f (c1 n)).monotone
          apply c2.monotone h
      }
      let chain_outer : Chain Y := {
        toFun := fun n => ωSup (chain_inner n)
        monotone' := by
          intro i j h
          apply ωSup_le; intro m
          apply le_trans (b := f (c1 j) (c2 m))
          · apply f.monotone
            apply c1.monotone h
          · apply le_ωSup (chain_inner j) m
      }
      have h_lhs : (f (ωSup c).1) (ωSup c).2 = ωSup chain_outer := by
        have h1 : (ωSup c).1 = ωSup c1 := rfl
        have h2 : (ωSup c).2 = ωSup c2 := rfl
        rw [h1, h2]
        have hf_cont := f.1.map_ωSup' c1
        change (f.1.toFun (ωSup c1)) (ωSup c2) = _
        rw [hf_cont]
        have h_pointwise : ∀ x, (ωSup (c1.map f.1.toOrderHom)) x =
            ωSup { toFun := fun n => f (c1 n) x,
                   monotone' := fun i j h => f.monotone (c1.monotone h) x } := by
          intro x
          rfl
        rw [h_pointwise]
        congr; funext n
        have h_fn_cont := (f (c1 n)).1.map_ωSup' c2
        exact h_fn_cont
      rw [h_lhs]
      apply le_antisymm
      · apply ωSup_le; intro n
        apply ωSup_le; intro m
        let k := max n m
        apply le_trans (b := f (c1 k) (c2 k))
        · apply le_trans (b := f (c1 n) (c2 k))
          · apply (f (c1 n)).monotone
            apply c2.monotone
            apply le_max_right
          · apply f.monotone
            apply c1.monotone
            apply le_max_left
        · convert le_ωSup _ k; rfl
      · apply ωSup_le; intro k
        apply le_trans (b := ωSup (chain_inner k))
        · apply le_ωSup (chain_inner k) k
        · apply le_ωSup chain_outer k
  }, by
    change IsHom (fun p : Z × X => (f p.1) p.2)
    refine isHom_comp (hf := isHom_eval) (g := fun p : Z × X => (f p.1, p.2)) ?_
    apply Prod.isHom_mk
    · apply isHom_comp (hf := f.2) (hg := Prod.isHom_fst)
    · exact Prod.isHom_snd
  ⟩

@[simp]
lemma curry_uncurry (f : Z →ω𝒒 (X →ω𝒒 Y)) : curry (uncurry f) = f := by
  ext; rfl

@[simp]
lemma uncurry_curry (f : Z × X →ω𝒒 Y) : uncurry (curry f) = f := by
  ext; rfl

end OmegaHom

end QuasiBorelSpaces
