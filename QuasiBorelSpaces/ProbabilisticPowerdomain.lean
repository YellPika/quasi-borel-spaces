import QuasiBorelSpaces.Option
import QuasiBorelSpaces.ENNReal
import QuasiBorelSpaces.OmegaQuasiBorelSpace
import QuasiBorelSpaces.OmegaHom
import QuasiBorelSpaces.OmegaCompletePartialOrder.Option
import QuasiBorelSpaces.OmegaCompletePartialOrder.Basic
import QuasiBorelSpaces.Basic
import QuasiBorelSpaces.Subtype
import QuasiBorelSpaces.Prop
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Probabilistic powerdomain (sections 4.1–4.4)

This file follows Sections 4.1–4.4 of [VakarKS19].
It records the basic structures (randomizations, expectation operators,
sampling, scoring, closures under ω-sups).
-/

namespace QuasiBorelSpaces

open MeasureTheory
open OmegaCompletePartialOrder
open QuasiBorelSpace

noncomputable section

/-
## The source of randomness
-/

/-- Reals with the Lebesgue measure and a discrete ωCPO structure -/
structure R where
  /-- The underlying real number -/
  val : ℝ

instance : Inhabited R := ⟨⟨0⟩⟩

instance : MeasurableSpace R :=
  MeasurableSpace.comap R.val (inferInstance : MeasurableSpace ℝ)

/-- Pull back the Lebesgue measure along `val` -/
instance : MeasureSpace R where
  volume := Measure.comap R.val volume

noncomputable instance : SigmaFinite (volume : Measure R) := by
  sorry

instance : QuasiBorelSpace R := QuasiBorelSpace.ofMeasurableSpace

instance : IsHom R.mk := isHom_of_measurable (f := R.mk) (by
  intro s hs
  rcases hs with ⟨t, ht, rfl⟩
  exact ht)

instance : IsHom R.val := isHom_of_measurable (f := R.val) (by
  intro s hs
  exact ⟨s, hs, rfl⟩)

/-- Discrete order on the randomness carrier -/
instance : PartialOrder R where
  le x y := x = y
  le_refl _ := rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm _ _ h₁ _ := h₁

/-- Trivial ωCPO on `R`: chains are constant by discreteness -/
noncomputable instance : OmegaCompletePartialOrder R where
  ωSup c := c 0
  le_ωSup c n := by
    rw [c.monotone (Nat.zero_le n)]
  ωSup_le c x hx := by
    rw [← hx 0]

/-- ωQBS structure on `R` (compatibility axiom holds vacuously) -/
noncomputable instance : OmegaQuasiBorelSpace R where
  isHom_ωSup := by
    intro c hc
    exact hc 0

/-- ωCPO on extended non-negative reals using the usual supremum of a chain -/
noncomputable instance instOmegaCompletePartialOrderENNReal :
    OmegaCompletePartialOrder ENNReal where
  ωSup c := sSup (Set.range c)
  le_ωSup c n := le_sSup ⟨n, rfl⟩
  ωSup_le c x hx := sSup_le (by rintro _ ⟨n, rfl⟩; exact hx n)

/-- ωQBS structure on `ENNReal` -/
noncomputable instance : OmegaQuasiBorelSpace ENNReal where
  isHom_ωSup := by
    intro c hc
    rw [isHom_iff_measurable]
    have : ωSup c = fun r => ⨆ n, c n r := by ext; rfl
    rw [this]
    apply Measurable.iSup
    intro n
    rw [← isHom_iff_measurable]
    exact hc n

/-- Trivial ωQBS on the unit type -/
instance : OmegaCompletePartialOrder Unit where
  ωSup _ := ()
  le_ωSup _ _ := trivial
  ωSup_le _ _ _ := trivial

instance : OmegaQuasiBorelSpace Unit where
  isHom_ωSup := by
    intro c hc
    apply isHom_const

/-
## Ambient ωQBSes for the construction
-/

variable (X : Type*) [OmegaQuasiBorelSpace X]

/-- ωQBS structure on lifted values -/
noncomputable instance instOmegaQuasiBorelSpaceOption :
    OmegaQuasiBorelSpace (Option X) where
  isHom_ωSup := by
    intro c hc
    sorry

/-
## Randomizations and expectation operators (Section 4.1)
-/

/-- Randomizations of `X` are partial maps from the randomness source -/
abbrev RX := R →ω𝒒 Option X

/-- Expectation operators on `X` (the Giry-style exponential) -/
abbrev JX := (X →ω𝒒 ENNReal) →ω𝒒 ENNReal

/-- Lift a weight to a partial result -/
def liftWeight (w : X → ENNReal) : Option X → ENNReal
  | some x => w x
  | none => 0

/-- Domain of a randomization -/
def dom (α : RX X) : Set R := {r | α r ≠ none}

/-- Evaluate the expectation of a weight under a randomization -/
def E_map (α : RX X) (w : X →ω𝒒 ENNReal) : ENNReal :=
  ∫⁻ r, liftWeight X (fun x => w x) (α r)

/-- Bundle the expectation operator arising from a randomization -/
def E_op (α : RX X) : JX X :=
  ⟨{ toFun := fun w => E_map (X := X) α w
     monotone' := by
       intro w1 w2 h
       simp only [E_map]
       apply lintegral_mono
       intro r
       dsimp [liftWeight]
       cases h_eq : α r with
       | none => apply le_refl
       | some x => exact h x
     map_ωSup' := by
       intro c
       simp only [E_map]
       have h_sup : ∀ r, liftWeight X (fun x =>
        (ωSup c) x) (α r) = ⨆ n, liftWeight X (fun x => c n x) (α r) := by
         intro r
         dsimp [liftWeight]
         cases α r with
         | none =>
           simp only [iSup_const]
         | some x =>
           have : (ωSup c) x = ⨆ n, c n x := rfl
           simp only [this]
       conv =>
         lhs
         arg 2
         intro r
         rw [h_sup]
       rw [lintegral_iSup]
       · congr
       · intro n
         have h_eq : (fun r => liftWeight X (fun x => c n x) (α r)) = (fun r =>
          Option.elim (α r) 0 (fun x => c n x)) := by
           ext r
           dsimp [liftWeight, Option.elim]
           cases α r <;> rfl
         rw [h_eq]
         have h_hom : IsHom (fun r => Option.elim (α r) 0 (fun x => c n x)) := by
           apply QuasiBorelSpace.Option.isHom_elim α.2
           · fun_prop
           · apply isHom_comp (c n).2
             fun_prop
         let f := fun r => Option.elim (α r) 0 (fun x => c n x)
         change Measurable f
         let f' := f ∘ R.mk
         have h_mk : IsHom R.mk := isHom_of_measurable (f := R.mk) (by
           intro s hs
           rcases hs with ⟨t, ht, rfl⟩
           exact ht)
         have : IsHom f' := isHom_comp h_hom h_mk
         have hf' : Measurable f' := measurable_of_isHom _ this
         have h_val : Measurable R.val := by
           intro s hs
           exact ⟨s, hs, rfl⟩
         rw [show f = f' ∘ R.val by ext; rfl]
         exact Measurable.comp hf' h_val
       · intro n m hnm r
         dsimp [liftWeight]
         cases α r with
         | none => apply le_refl
         | some x => apply c.monotone hnm
    }, by
     rw [QuasiBorelSpace.isHom_def]
     intro β hβ
     rw [isHom_iff_measurable]
     dsimp

     let F := fun (p : ℝ × R) => liftWeight X (β p.1) (α p.2)
     change Measurable (fun r => ∫⁻ s, F (r, s) ∂volume)

     apply Measurable.lintegral_prod_right

     have hF_hom : IsHom F := by
       have h_eq : F = (fun (p : ℝ × R) => Option.elim (α p.2) 0 (fun x => (β p.1) x)) := by
         dsimp [F]
         ext p
         dsimp [liftWeight, Option.elim]
         cases α p.2 <;> rfl
       rw [h_eq]
       apply QuasiBorelSpace.Option.isHom_elim
       · apply isHom_comp α.2
         exact Prod.isHom_snd
       · fun_prop
       · have h_uncurry : IsHom (Function.uncurry (fun r x => β r x)) := by
           rw [OmegaHom.isHom_def] at hβ
           exact hβ
         change IsHom ((Function.uncurry fun r x ↦ (β r) x) ∘ (fun p : (ℝ × R) × X => (p.1.1, p.2)))
         apply isHom_comp h_uncurry
         apply Prod.isHom_mk
         · apply isHom_comp Prod.isHom_fst
           exact Prod.isHom_fst
         · exact Prod.isHom_snd

     let f' : ℝ × ℝ → ENNReal := F ∘ (Prod.map (id : ℝ → ℝ) R.mk)
     have h_mk : IsHom R.mk := isHom_of_measurable (f := R.mk) (by
       intro s hs
       rcases hs with ⟨t, ht, rfl⟩
       exact ht)
     have h_map : IsHom (Prod.map (id : ℝ → ℝ) R.mk) := by
       apply Prod.isHom_mk
       · apply isHom_comp isHom_id Prod.isHom_fst
       · apply isHom_comp h_mk Prod.isHom_snd
     have : IsHom f' := isHom_comp hF_hom h_map
     have hf' : Measurable f' := by sorry
     have h_val : Measurable R.val := by
       intro s hs
       exact ⟨s, hs, rfl⟩
     have h_map_val : Measurable (Prod.map (id : ℝ → ℝ) R.val) := by
       apply Measurable.prodMk
       · apply Measurable.comp measurable_id measurable_fst
       · apply Measurable.comp h_val measurable_snd
     rw [show F = f' ∘ (Prod.map (id : ℝ → ℝ) R.val) by ext; rfl]
     have : MeasurableSpace (ℝ × R) := inferInstance
     exact sorry
   ⟩

/-- The expectation morphism `E : RX → JX` -/
def E : RX X →ω𝒒 JX X :=
  ⟨{ toFun := fun α => E_op (X := X) α
     monotone' := by
      intro x y hxy k
      simp only [E_op, E_map, liftWeight, OrderHom.toFun_eq_coe, OrderHom.coe_mk]
      apply lintegral_mono
      intro z
      simp only
      cases hx : x z with
      | none => simp only [zero_le]
      | some xz =>
        cases hy : y z with
        | none =>
          specialize hxy z
          change x.val z = some xz at hx
          change y.val z = none at hy
          simp only [OrderHom.toFun_eq_coe, ContinuousHom.coe_toOrderHom, hx, hy] at hxy
          cases hxy
        | some yz =>
          simp only
          apply k.monotone
          specialize hxy z
          change x.val z = some xz at hx
          change y.val z = some yz at hy
          simp only [OrderHom.toFun_eq_coe, ContinuousHom.coe_toOrderHom, hx, hy] at hxy
          apply hxy
     map_ωSup' := by
       intro c
       apply OmegaHom.ext
       intro w
       sorry
    }, by
      sorry⟩

/-- Monad unit on randomizations (Dirac) -/
def return_R (x : X) : RX X :=
  ⟨{ toFun := fun r => if r.val ∈ Set.Icc 0 1 then some x else none
     monotone' := by
       intro r s hrs
       rw [hrs]
     map_ωSup' := by
       intro c
       let f : R →o Option X := {
         toFun := fun r => if r.val ∈ Set.Icc 0 1 then some x else none
         monotone' := by
           intro r s hrs
           rw [hrs]
       }
       have h_const : ∀ n, c n = c 0 := fun n => (c.monotone (Nat.zero_le n)).symm
       have h_map : c.map f = Chain.const (f (c 0)) := by
         ext n
         simp [h_const n]
       rw [h_map]
       simp only [ωSup_const]
       congr 1
    }, by
      classical
      change IsHom (fun (r : R) => if r.val ∈ Set.Icc 0 1 then some x else none)
      apply QuasiBorelSpace.Prop.isHom_ite
      · change IsHom ((fun (v : ℝ) => v ∈ Set.Icc 0 1) ∘ R.val)
        apply QuasiBorelSpace.isHom_comp
        · rw [isHom_iff_measurable]
          intro s _
          let S : Set ℝ := {v | (v ∈ Set.Icc (0:ℝ) 1) ∈ s}
          have hS : MeasurableSet S := by
            by_cases hT : True ∈ s <;> by_cases hF : False ∈ s
            · suffices S = Set.univ by rw [this]; exact MeasurableSet.univ
              dsimp [S]
              ext v
              simp only [Set.mem_Icc]
              by_cases hv : 0 ≤ v ∧ v ≤ 1
              · simp [hv, hT]
              · simp [hv, hF]
            · suffices S = Set.Icc 0 1 by rw [this]; exact measurableSet_Icc
              dsimp [S]
              ext v
              simp only [Set.mem_Icc]
              by_cases hv : 0 ≤ v ∧ v ≤ 1
              · simp [hv, hT]
              · simp [hv, hF]
            · suffices S = (Set.Icc 0 1)ᶜ by rw [this]; exact MeasurableSet.compl measurableSet_Icc
              dsimp [S]
              ext v
              simp only [Set.mem_Icc]
              by_cases hv : 0 ≤ v ∧ v ≤ 1
              · simp [hv, hT]
              · simp [hv, hF]
            · suffices S = ∅ by rw [this]; exact MeasurableSet.empty
              dsimp [S]
              ext v
              simp only [Set.mem_Icc]
              by_cases hv : 0 ≤ v ∧ v ≤ 1
              · simp [hv, hT]
              · simp [hv, hF]
          exact hS
        · apply isHom_of_measurable
          intro s hs
          exact ⟨s, hs, rfl⟩
      · apply isHom_const
      · apply isHom_const
    ⟩

/-- A measurable splitting of randomness as in the transfer principle -/
class RandomSplit where
  /-- The splitting function -/
  φ : R → R × R
  /-- The splitting function is measurable -/
  measurable_φ : Measurable φ
  /-- Pushing forward Lebesgue along the split yields the product measure -/
  preserves_volume :
    Measure.map φ (volume : Measure R) =
      (volume : Measure R).prod (volume : Measure R)

/-- A default instance of `RandomSplit` (placeholder for now) -/
noncomputable def defaultRandomSplit : RandomSplit := by
  classical
  refine ⟨?φ, ?hφ, ?hpres⟩
  · sorry
  · sorry
  · sorry

attribute [instance] defaultRandomSplit

variable [RandomSplit]

/-- Monad bind on randomizations using the randomness splitting -/
def bind_R {Y} [OmegaQuasiBorelSpace Y] (α : RX X) (k : X → RX Y) : RX Y where
  val := {
    toFun r :=
      match RandomSplit.φ r with
      | (r₁, r₂) => α r₁ >>= (k · r₂)
    monotone' := by
      intro r s hrs
      cases hrs
      exact le_rfl
    map_ωSup' := by
      intro c
      have hc : ∀ n, c n = c 0 := fun n => (c.monotone (Nat.zero_le n)).symm
      rw [show ωSup c = c 0 from rfl]
      symm
      let f : R →o Option Y := {
        toFun := fun r => match RandomSplit.φ r with | (r₁, r₂) => α r₁ >>= (k · r₂)
        monotone' := by
          intro r s hrs
          cases hrs
          exact le_rfl
      }
      change ωSup (c.map f) = f (c 0)
      have : c.map f = Chain.const (f (c 0)) := by
        ext n
        simp [hc]
      rw [this]
      apply ωSup_const
  }

  property := by
      sorry

end

section ExpectationMonad

variable (X : Type*) [OmegaQuasiBorelSpace X]

/-
## Expectation monad (See Section 4.1 of [VakarKS19])
-/

/-- Monad unit on expectation operators -/
def return_J (x : X) : JX X :=
  ⟨{ toFun := fun w => w x
     monotone' := by
       intro w₁ w₂ hw
       exact hw x
     map_ωSup' := by
       intro c
       rfl
    }, by
      change IsHom ((fun p : (X →ω𝒒 ENNReal) × X => p.1 p.2) ∘ (fun w => (w, x)))
      apply isHom_comp (hf := OmegaHom.isHom_eval)
      apply Prod.isHom_mk
      · exact isHom_id
      · exact isHom_const x
    ⟩

/-- Monad bind on expectation operators -/
def bind_J {Y} [OmegaQuasiBorelSpace Y] (μ : JX X) (k : X → JX Y) : JX Y :=
  ⟨{ toFun := fun w => μ ⟨{ toFun := fun x => k x w
                            monotone' := by
                              intro x y hxy
                              sorry
                            map_ωSup' := by
                              intro c
                              sorry
                          }, by
                            sorry⟩
     monotone' := by
       intro w₁ w₂ hw
       sorry
     map_ωSup' := by
       intro c
       sorry
   }, by
     sorry⟩

lemma return_bind_J {Y} [OmegaQuasiBorelSpace Y] {x : X} {f : X → JX Y}
    : bind_J _ (return_J _ x) f = f x := by
  apply OmegaHom.ext
  intro w
  rfl

lemma bind_return_J {Y} [OmegaQuasiBorelSpace Y] {x : JX X}
    : bind_J _ x (return_J _) = x := by
  apply OmegaHom.ext
  intro w
  rfl

lemma bind_bind_J
    {Y Z} [OmegaQuasiBorelSpace Y] [OmegaQuasiBorelSpace Z]
    {x : JX X} {f : X → JX Y} {g : Y → JX Z}
    : bind_J _ (bind_J _ x f) g = bind_J _ x fun y ↦ bind_J _ (f y) g := by
  apply OmegaHom.ext
  intro w
  rfl

/-- Expectation preserves the monad structure on randomizations -/
theorem E_preserves_return (x : X) :
    E (X := X) (return_R (X := X) x) = return_J (X := X) x := by
  apply OmegaHom.ext
  intro w
  change E_map X (return_R X x) w = w x
  unfold E_map return_R
  dsimp [liftWeight]

  let e : R ≃ᵐ ℝ := {
    toFun := R.val
    invFun := R.mk
    left_inv := fun r => rfl
    right_inv := fun y => rfl
    measurable_toFun := Measurable.of_comap_le le_rfl
    measurable_invFun := by
      intro s hs
      rcases hs with ⟨t, ht, rfl⟩
      simpa using ht
  }

  have h_vol_def : (volume : Measure R) = Measure.comap R.val volume := rfl
  have h_vol : (volume : Measure R) = Measure.map e.symm volume := by
    rw [h_vol_def]
    ext s hs
    rw [Measure.map_apply e.symm.measurable hs]
    rw [Measure.comap_apply]
    · congr
      ext y
      simp
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact hr
      · intro hy
        use R.mk y
        constructor
        · exact hy
        · rfl
    · exact e.injective
    · intro s' hs'
      change MeasurableSet (e '' s')
      rw [MeasurableEquiv.image_eq_preimage_symm]
      exact e.symm.measurable hs'
    · exact hs

  simp [h_vol]
  let g := fun r => liftWeight X (fun x => w x) (return_R X x r)
  have h_eq : ∫⁻ r, g r ∂(Measure.map e.symm volume) = ∫⁻ y, g (e.symm y) ∂volume := by
    exact lintegral_map_equiv g e.symm

  change ∫⁻ r, g r ∂(Measure.map e.symm volume) = w x
  rw [h_eq]
  have h_int : (fun y => g (e.symm y)) =
      (fun y => w x * Set.indicator (Set.Icc 0 1) (fun _ => 1) y) := by
    ext y
    simp only [g, return_R, liftWeight, Set.indicator]
    change (match (if (e.symm y).val ∈ Set.Icc 0 1 then some x else none) with
      | some x => w x | none => 0) = _
    have : (e.symm y).val = y := rfl
    rw [this]
    split_ifs <;> simp
  rw [h_int]
  rw [lintegral_const_mul]
  · rw [lintegral_indicator_const measurableSet_Icc 1]
    rw [Real.volume_Icc]
    simp
  · exact Measurable.indicator measurable_const measurableSet_Icc

theorem E_preserves_bind {Y} [OmegaQuasiBorelSpace Y] (α : RX X) (k : X → RX Y) :
    E (X := Y) (bind_R (X := X) (Y := Y) α k) =
      bind_J (X := X) (Y := Y) (E (X := X) α) (fun x => E (X := Y) (k x)) := by
  sorry

/-
## Randomizable operators and ω-closures (See Section 4.2 of [VakarKS19])
-/

/-- Predicate: expectation operator arising from a randomization -/
def Randomizable (μ : JX X) : Prop := ∃ α : RX X, μ = E_op (X := X) α

/-- Randomizable expectation operators as a subtype -/
def SX := {μ : JX X // Randomizable (X := X) μ}
/-- Randomizations valued in randomizations -/
abbrev MRX := R →ω𝒒 RX X
/-- Randomizable random operators (random elements of `JX`) -/
abbrev MSX := R →ω𝒒 JX X

/-- Extend `E` pointwise to random randomizations -/
noncomputable def E_rand (β : MRX X) : MSX X :=
  ⟨{ toFun := fun r => E_op (X := X) (β r)
     monotone' := by
       intro r s hrs
       cases hrs
       exact le_rfl
     map_ωSup' := by
       intro c
       let f : OrderHom R (JX X) :=
         { toFun := fun r => E_op (X := X) (β r)
           monotone' := by
             intro r s hrs
             cases hrs
             exact le_rfl }
       have h_sup : ωSup c = c 0 := rfl
       apply le_antisymm
       · have : f (ωSup c) ≤ ωSup (c.map f) :=
           le_ωSup (c.map f) 0
         simpa [h_sup] using this
       · apply ωSup_le
         intro n
         have hconst : c n = c 0 := by
           have h' : c 0 = c n := c.monotone (Nat.zero_le n)
           exact h'.symm
         simp [h_sup, hconst]
    }, by
      sorry⟩

/-- Membership in the ω-sup-closure of randomizable operators -/
inductive InTX : JX X → Prop
  /-- Randomizable operators are in the closure -/
  | randomizable (α : RX X) : InTX (E_op (X := X) α)
  /-- The closure is closed under ω-sups -/
  | sup {c : Chain (JX X)} : (∀ n, InTX (c n)) → InTX (ωSup c)

/-- Membership in the ω-sup-closure of randomizable random operators -/
inductive InMTX : MSX X → Prop
  /-- Randomizable random operators are in the closure -/
  | randomizable (β : MRX X) : InMTX (E_rand (X := X) β)
  /-- The closure is closed under ω-sups -/
  | sup {c : Chain (MSX X)} : (∀ n, InMTX (c n)) → InMTX (ωSup c)

/-- Probabilistic powerdomain: smallest ω-subcpo of `JX` -/
abbrev TX := {μ : JX X // InTX (X := X) μ}

/-- Random elements of the powerdomain -/
abbrev MTX := {β : MSX X // InMTX (X := X) β}

/-- Order structure on `T X` inherited from the ambient `JX` -/
noncomputable instance : PartialOrder (TX X) := inferInstance

/-- Order structure on `M T X` inherited from the ambient `M JX` -/
noncomputable instance : PartialOrder (MTX X) := inferInstance

/- Forgetful inclusions -/
section Inclusions

/-- Inclusion of `TX` into `JX` -/
def TX.incl (t : TX X) : JX X := t.1

/-- Inclusion of `MTX` into `MSX` -/
def MTX.incl (t : MTX X) : MSX X := t.1

end Inclusions

/-- Expectation factors through `T` -/
noncomputable def E_T (α : RX X) : TX X :=
  ⟨E_op (X := X) α, InTX.randomizable α⟩

/-- Pointwise extension of `E_T` to random randomizations -/
noncomputable def E_MT (β : MRX X) : MTX X :=
  ⟨E_rand (X := X) β, InMTX.randomizable β⟩

/-- `TX` inherits an ωCPO structure from `JX` -/
noncomputable instance : OmegaCompletePartialOrder (TX X) :=
{ (inferInstance : PartialOrder (TX X)) with
    ωSup := fun c =>
      let incl : OrderHom (TX X) (JX X) :=
        { toFun := Subtype.val
          monotone' := by
            intro a b h
            exact h }
      ⟨ωSup (c.map incl), InTX.sup (fun n => (c n).2)⟩
    le_ωSup := by
      intro c n
      simpa using (le_ωSup (c.map ⟨Subtype.val, by intro a b h; exact h⟩) n)
    ωSup_le := by
      intro c x hx
      exact (ωSup_le (c := c.map ⟨Subtype.val, by intro a b h; exact h⟩) (x := x.1)
        (by
          intro n
          exact hx n)) }

/-- `TX` is an ωQBS as a full subobject of `JX` -/
noncomputable instance : OmegaQuasiBorelSpace (TX X) :=
{ (inferInstance : OmegaCompletePartialOrder (TX X)),
  (inferInstance : QuasiBorelSpace (TX X)) with
    isHom_ωSup := by
      intro c hc
      -- compatibility inherited from `JX`
      sorry }

/-- `MTX` inherits an ωCPO structure from `MSX` -/
noncomputable instance : OmegaCompletePartialOrder (MTX X) :=
{ (inferInstance : PartialOrder (MTX X)) with
    ωSup := fun c =>
      let incl : OrderHom (MTX X) (MSX X) :=
        { toFun := Subtype.val
          monotone' := by
            intro a b h
            exact h }
      ⟨ωSup (c.map incl), InMTX.sup (fun n => (c n).2)⟩
    le_ωSup := by
      intro c n
      simpa using (le_ωSup (c.map ⟨Subtype.val, by intro a b h; exact h⟩) n)
    ωSup_le := by
      intro c x hx
      exact (ωSup_le (c := c.map ⟨Subtype.val, by intro a b h; exact h⟩) (x := x.1)
        (by
          intro n
          exact hx n)) }

/-- `MTX` is an ωQBS as a full subobject of `MSX` -/
noncomputable instance : OmegaQuasiBorelSpace (MTX X) :=
{ (inferInstance : OmegaCompletePartialOrder (MTX X)),
  (inferInstance : QuasiBorelSpace (MTX X)) with
    isHom_ωSup := by
      intro c hc
      sorry }

/-- Monad unit on `T` obtained by restriction -/
def return_T (x : X) : TX X :=
  ⟨return_J (X := X) x, by
    rw [←E_preserves_return]
    apply InTX.randomizable⟩

/-- Monad bind on `T`, restricting the `J` bind -/
def bind_T {Y} [OmegaQuasiBorelSpace Y] (t : TX X) (k : X → TX Y) : TX Y :=
  ⟨bind_J (X := X) (Y := Y) t.1 (fun x => (k x).1), by
    sorry⟩

/-- (placeholder) The inclusion `T ↪ J` is a monad morphism (See theorem 4.3 of [VakarKS19]) -/
theorem expectation_factorizes_monad :
    True := by
  trivial

/-
## Sampling and conditioning (Section 4.4)
-/

/-- `sample : 1 → R R` is the identity randomization on reals -/
noncomputable def sample_map (_ : Unit) : RX R :=
  ⟨{ toFun := fun r => if r.val ∈ Set.Icc 0 1 then some r else none
     monotone' := by
       intro _ _ h
       cases h
       rfl
     map_ωSup' := by
       intro c
       let f : OrderHom R (Option R) :=
         { toFun := some
           monotone' := by
             intro r s hrs
             cases hrs
             rfl }
       have hconst : ∀ n, c n = c 0 := fun n => (c.monotone (Nat.zero_le n)).symm
       have hmap_const : c.map f = Chain.const (some (c 0)) := by
         ext n
         simp [Chain.map_coe, f, hconst n]
       sorry
      --  calc
      --    some (ωSup c) = some (c 0) := by rfl
      --    _ = ωSup (Chain.const (some (c 0))) := by
      --          simp only [ωSup_const]
      --    _ = ωSup (c.map f) := by simp [hmap_const]
    }, by
      sorry
      -- apply QuasiBorelSpace.Option.isHom_some
      -- exact isHom_id
    ⟩

/-- `score : R → R⊥` truncates Lebesgue to an interval of length `|r|` -/
noncomputable def score_map (r : R) : RX Unit :=
  ⟨{ toFun := fun t =>
       if t.val ∈ Set.Icc (0 : ℝ) |r.val| then some () else none
     monotone' := by
       intro t1 t2 h
       rw [h]
     map_ωSup' := by
       intro c
       have h_eq : ∀ n, c n = c 0 := fun n => (c.monotone (Nat.zero_le n)).symm
       have h_sup : ωSup c = c 0 := rfl
       rw [h_sup]
       let f : R →o Option Unit := {
         toFun := fun t => if t.val ∈ Set.Icc 0 |r.val| then some () else none
         monotone' := by intro t1 t2 h; rw [h]
       }
       change f (c 0) = ωSup (c.map f)
       apply le_antisymm
       · exact le_ωSup (c.map f) 0
       · apply ωSup_le
         try intro n
         try dsimp
         try rw [h_eq n]
         try apply le_refl
    }, by
      change IsHom (fun (t : R) => if t.val ∈ Set.Icc 0 |r.val| then some () else none)
      apply QuasiBorelSpace.Prop.isHom_ite
      · change IsHom ((fun x => x ∈ Set.Icc 0 |r.val|) ∘ R.val)
        apply QuasiBorelSpace.isHom_comp
        · rw [isHom_iff_measurable]
          intro t _
          by_cases hT : True ∈ t <;> by_cases hF : False ∈ t
          · suffices (fun x => x ∈ Set.Icc 0 |r.val|) ⁻¹' t = Set.univ by
              rw [this]; exact MeasurableSet.univ
            ext x; simp; by_cases h : x ∈ Set.Icc 0 |r.val|
            · simp only [Set.mem_Icc] at h; rw [eq_true h]; exact hT
            · simp only [Set.mem_Icc] at h; rw [eq_false h]; exact hF
          · suffices (fun x => x ∈ Set.Icc 0 |r.val|) ⁻¹' t = Set.Icc 0 |r.val| by
              rw [this]; exact measurableSet_Icc
            ext x; simp; by_cases h : x ∈ Set.Icc 0 |r.val|
            · simp only [Set.mem_Icc] at h; rw [eq_true h]; simp [hT]
            · simp only [Set.mem_Icc] at h; rw [eq_false h]; simp [hF]
          · suffices (fun x => x ∈ Set.Icc 0 |r.val|) ⁻¹' t = (Set.Icc 0 |r.val|)ᶜ by
              rw [this]; exact MeasurableSet.compl measurableSet_Icc
            ext x; simp; by_cases h : x ∈ Set.Icc 0 |r.val|
            · simp only [Set.mem_Icc] at h; rw [eq_true h]; simp [hT]; assumption
            · simp only [Set.mem_Icc] at h; rw [eq_false h]; simp [hF]
              intro hx; simp [hx] at h; exact h
          · suffices (fun x => x ∈ Set.Icc 0 |r.val|) ⁻¹' t = ∅ by
              rw [this]; exact MeasurableSet.empty
            ext x; simp; by_cases h : x ∈ Set.Icc 0 |r.val|
            · simp only [Set.mem_Icc] at h; rw [eq_true h]; exact hT
            · simp only [Set.mem_Icc] at h; rw [eq_false h]; exact hF
        · apply isHom_of_measurable
          exact Measurable.of_comap_le le_rfl
      · apply isHom_const
      · apply isHom_const
    ⟩

/-- Sampling lifted to the powerdomain -/
noncomputable def sample_T (_ : Unit) : TX R :=
  E_T (X := R) (sample_map ())

/-- Conditioning lifted to the powerdomain -/
noncomputable def score_T (r : R) : TX Unit :=
  E_T (X := Unit) (score_map r)

end ExpectationMonad
end QuasiBorelSpaces
