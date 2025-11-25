import QuasiBorelSpaces.Option
import QuasiBorelSpaces.ENNReal
import QuasiBorelSpaces.OmegaQuasiBorelSpace
import QuasiBorelSpaces.OmegaHom
import QuasiBorelSpaces.OmegaCompletePartialOrder.Option
import QuasiBorelSpaces.OmegaCompletePartialOrder.Basic
import QuasiBorelSpaces.Basic
import QuasiBorelSpaces.Subtype
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
  ∫⁻ r in dom (X := X) α, (liftWeight (w := fun x => w x)) (α r)

/-- Bundle the expectation operator arising from a randomization -/
def E_op (α : RX X) : JX X :=
  ⟨{ toFun := fun w => E_map (X := X) α w
     monotone' := by
       intro w1 w2 h
       simp only [E_map]
       apply lintegral_mono
       intro r
       dsimp
       cases h_eq : α r with
       | none =>
         dsimp [liftWeight]
         apply le_refl
       | some x =>
         dsimp [liftWeight]
         exact h x
     map_ωSup' := by
       sorry
    }, by
      sorry⟩

/-- The expectation morphism `E : RX → JX` -/
def E : RX X →ω𝒒 JX X :=
  ⟨{ toFun := fun α => E_op (X := X) α
     monotone' := by
       sorry
     map_ωSup' := by
       sorry
    }, by
      sorry⟩

/-- Monad unit on randomizations (Dirac) -/
def return_R (x : X) : RX X :=
  ⟨{ toFun := fun _ => some x
     monotone' := by
       intro _ _ _
       rfl
     map_ωSup' := by
       intro c
       conv_lhs => rw [← OmegaCompletePartialOrder.ωSup_const (some x)]
       congr 1
    }, by
      apply isHom_const
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
def bind_R {Y} [OmegaQuasiBorelSpace Y] (α : RX X) (k : X → RX Y) : RX Y :=
  ⟨{ toFun := fun r =>
       match RandomSplit.φ r with
       | (r₁, r₂) =>
           match α r₁ with
           | none => none
           | some x => k x r₂
     monotone' := by
       intro r s hrs
       sorry
     map_ωSup' := by
       intro c
       sorry
    }, by
      sorry⟩

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

/-- Expectation preserves the monad structure on randomizations -/
theorem E_preserves_return (x : X) :
    E (X := X) (return_R (X := X) x) = return_J (X := X) x := by
  sorry

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
       sorry
     map_ωSup' := by
       intro c
       sorry
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
      ⟨ωSup (c.map incl), sorry⟩
    le_ωSup := by
      intro c n
      sorry
    ωSup_le := by
      intro c x hx
      sorry }

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
      ⟨ωSup (c.map incl), sorry⟩
    le_ωSup := by
      intro c n
      sorry
    ωSup_le := by
      intro c x hx
      sorry }

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
    sorry⟩

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
def sample_map (_ : Unit) : RX R :=
  ⟨{ toFun := fun r => some r
     monotone' := by
       intro _ _ h
       simpa [h]
     map_ωSup' := by
       intro c
       sorry
    }, by
      sorry⟩

/-- `score : R → R⊥` truncates Lebesgue to an interval of length `|r|` -/
noncomputable def score_map (r : R) : RX Unit :=
  ⟨{ toFun := fun t =>
       if ht : t.val ∈ Set.Icc (0 : ℝ) |r.val| then some () else none
     monotone' := by
       intro _ _ _
       sorry
     map_ωSup' := by
       intro c
       sorry
    }, by
      sorry⟩

/-- Sampling lifted to the powerdomain -/
noncomputable def sample_T (_ : Unit) : TX R :=
  E_T (X := R) (sample_map ())

/-- Conditioning lifted to the powerdomain -/
noncomputable def score_T (r : R) : TX Unit :=
  E_T (X := Unit) (score_map r)

/-
## Free monad viewpoint (See Section 4.4 of [VakarKS19])
-/

universe u

section FreeMonad

variable (F : Type → Type) [Monad F]
variable (sampleF : Unit → F R) (scoreF : R → F Unit)

/-- A simple notion of monad morphism used for the free-monad statement -/
structure MonadMorphismToT
    (F : Type → Type) [Monad F]
    (sampleF : Unit → F R) (scoreF : R → F Unit) where
  /-- The morphism maps the free monad to `TX` -/
  app :
    ∀ {Y} [OmegaQuasiBorelSpace Y] [Inhabited Y], F Y → TX Y
  /-- The morphism preserves the unit -/
  map_pure :
    ∀ {Y} [OmegaQuasiBorelSpace Y] [Inhabited Y] (y : Y),
      app (pure y) = return_T (X := Y) y
  /-- The morphism preserves the bind -/
  map_bind :
    ∀ {Y Z} [OmegaQuasiBorelSpace Y] [OmegaQuasiBorelSpace Z] [Inhabited Y] [Inhabited Z]
      (fy : F Y) (k : Y → F Z),
      app (fy >>= k) =
        bind_T (X := Y) (Y := Z) (app fy) (fun y => app (k y))
  /-- The morphism preserves the sample operation -/
  preserves_sample : app (sampleF ()) = sample_T ()
  /-- The morphism preserves the score operation -/
  preserves_score : ∀ r, app (scoreF r) = score_T r

/-- The monad morphism interpreting the free sampling/conditioning monad into `T` -/
noncomputable def m_T : MonadMorphismToT F sampleF scoreF :=
  { app := by
      intro Y _ _ fy
      exact ⟨return_J (X := Y) default, sorry⟩
    map_pure := by
      intro Y _ _ y
      sorry
    map_bind := by
      intro Y Z _ _ _ _ fy k
      sorry
    preserves_sample := by
      sorry
    preserves_score := by
      intro r
      sorry }

/-- The morphism `m_T` is component-wise densely strong epi (Lemma 4.4 placeholder) -/
theorem m_T_dense {Y} [OmegaQuasiBorelSpace Y] [Inhabited Y] :
    True := by
  trivial

end FreeMonad


end ExpectationMonad
end QuasiBorelSpaces
