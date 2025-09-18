import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import QuasiBorelSpaces.MeasureTheory.Cases

open scoped MeasureTheory

/--
A quasi‑borel space consists of a type `A` together with a set of "random
variables" in `ℝ → A` satisfying closure under constants, measurable
precomposition, and gluing along borel partitions.
-/
@[ext]
class QuasiBorelSpace (A : Type*) where
  /--
  `IsVar φ` denotes whether `φ` is a random variable. Variables can be
  approximately thought of as the measurable functions in `ℝ → A`.
  -/
  IsVar : (ℝ → A) → Prop

  /-- Variables are closed under constant functions. -/
  isVar_const (x : A) : IsVar (fun _ : ℝ ↦ x)

  /-- Variables are closed under precomposition with measurable functions. -/
  isVar_comp {f : ℝ → ℝ} {φ : ℝ → A}
    : Measurable f
    → IsVar φ
    → IsVar (fun r ↦ φ (f r))

  /-- Variables are closed under gluing of countable families. -/
  isVar_cases' {ix : ℝ → ℕ} {φ : ℕ → ℝ → A}
    : Measurable ix
    → (∀n, IsVar (φ n))
    → IsVar (fun r ↦ φ (ix r) r)

/--
A _measurable quasi-borel space_ is the quasi-borel space where the notion of
variable aligns with measurable functions.
-/
class MeasurableQuasiBorelSpace (A : Type*) [QuasiBorelSpace A] [MeasurableSpace A] where
  /-- Variables are measurable functions. -/
  isVar_iff_measurable (φ : ℝ → A) : QuasiBorelSpace.IsVar φ ↔ Measurable φ

/--
A _discrete quasi-borel space_ is the quasi-borel space analogue of the discrete
measurable space.
-/
class abbrev DiscreteQuasiBorelSpace (A : Type*) [QuasiBorelSpace A] [MeasurableSpace A] :=
  DiscreteMeasurableSpace A
  MeasurableQuasiBorelSpace A

namespace QuasiBorelSpace

attribute [fun_prop] IsVar isVar_const isVar_comp
attribute [simp] isVar_const

variable {A B : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B]

/--
A function `f : A → B` between `QuasiBorelSpace`s is a _morphism_ if it
preserves  variables under pre-composition.
-/
@[fun_prop]
def IsHom (f : A → B) : Prop :=
  ∀⦃φ⦄, IsVar φ → IsVar (fun x ↦ f (φ x))

@[inherit_doc IsHom]
notation "IsHom[" inst₁ ", " inst₂ "]" => @IsHom _ _ inst₁ inst₂

/-- Every `MeasurableSpace` induces a `QuasiBorelSpace`. -/
def ofMeasurableSpace [MeasurableSpace A] : QuasiBorelSpace A where
  IsVar φ := Measurable φ
  isVar_const x := measurable_const
  isVar_comp := by fun_prop
  isVar_cases' := MeasureTheory.measurable_cases

instance [MeasurableSpace A] : @MeasurableQuasiBorelSpace A ofMeasurableSpace _ :=
  @MeasurableQuasiBorelSpace.mk A ofMeasurableSpace _ fun _ ↦ by rfl

/-- Every `QuasiBorelSpace` induces a `MeasurableSpace`. -/
def toMeasurableSpace [QuasiBorelSpace A] : MeasurableSpace A where
  MeasurableSet' X := ∀{φ : ℝ → A}, IsVar φ → MeasurableSet (φ ⁻¹' X)
  measurableSet_empty hφ := by
    simp only [Set.preimage_empty, MeasurableSet.empty]
  measurableSet_compl X hX φ hφ := by
    simp only [Set.preimage_compl, MeasurableSet.compl_iff]
    apply hX
    apply hφ
  measurableSet_iUnion f hf φ hφ := by
    simp only [Set.preimage_iUnion]
    apply MeasurableSet.iUnion
    intro n
    apply hf
    apply hφ

/-- We can lift a `QuasiBorelSpace` from one type to another. -/
def lift [QuasiBorelSpace A] (f : B → A) : QuasiBorelSpace B where
  IsVar φ := IsVar fun x ↦ f (φ x)
  isVar_const x := isVar_const (f x)
  isVar_comp := isVar_comp
  isVar_cases' := isVar_cases'

@[simps!]
instance : Inhabited (QuasiBorelSpace A) where
  default := @ofMeasurableSpace _ ⊤

namespace Real

@[simps!]
instance : QuasiBorelSpace ℝ := ofMeasurableSpace

end Real

namespace ENNReal

@[simps!]
instance : QuasiBorelSpace ENNReal := ofMeasurableSpace

end ENNReal

end QuasiBorelSpace
