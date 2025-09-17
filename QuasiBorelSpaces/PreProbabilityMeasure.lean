import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.DiracProba
import QuasiBorelSpaces.Bool
import QuasiBorelSpaces.Hom
import QuasiBorelSpaces.MeasureTheory.Map
import QuasiBorelSpaces.MeasureTheory.ProbabilityMeasure
import QuasiBorelSpaces.Unit

open MeasureTheory
open scoped unitInterval

namespace QuasiBorelSpace

variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]
  {C : Type*} [QuasiBorelSpace C]
  {D : Type*} [QuasiBorelSpace D]

/--
A precursor to the type of probability measures. Intuitively, a
_(quasi-borel) probability measure_ is just a variable applied to a normal
probability measure on `ℝ`. A `PreProbabilityMeasure` holds the underlying
variable and probability measure.
-/
@[ext]
structure PreProbabilityMeasure (A : Type*) [QuasiBorelSpace A] where
  /-- The random variable associated with the probability measure. -/
  eval : ℝ →𝒒 A
  /-- The base `ProbabilityMeasure`. -/
  base : ProbabilityMeasure ℝ

namespace PreProbabilityMeasure

/-- The integral of a function relative to a probability measure. -/
noncomputable def lintegral (f : A → ENNReal) : PreProbabilityMeasure A → ENNReal
  | ⟨φ, μ⟩ => ∫⁻ x, f (φ x) ∂μ

@[simp]
alias lintegral_mk := PreProbabilityMeasure.lintegral.eq_1

lemma lintegral_add_left
    {f : A → ENNReal} (hf : IsHom f)
    (g : A → ENNReal) (μ : PreProbabilityMeasure A)
    : lintegral (f + g) μ = lintegral f μ + lintegral g μ := by
  rcases μ with ⟨eval, base⟩
  simp only [lintegral_mk, Pi.add_apply]
  apply MeasureTheory.lintegral_add_left
  apply hf
  simp only [QuasiBorelHom.isVar_coe]

lemma lintegral_add_right
    (f : A → ENNReal)
    {g : A → ENNReal} (hg : IsHom g)
    (μ : PreProbabilityMeasure A)
    : lintegral (f + g) μ = lintegral f μ + lintegral g μ := by
  rcases μ with ⟨eval, base⟩
  simp only [lintegral_mk, Pi.add_apply]
  apply MeasureTheory.lintegral_add_right
  apply hg
  simp only [QuasiBorelHom.isVar_coe]

instance setoid (A : Type*) [QuasiBorelSpace A] : Setoid (PreProbabilityMeasure A) where
  r μ₁ μ₂ := ∀⦃f⦄, IsHom f → μ₁.lintegral f = μ₂.lintegral f
  iseqv := {
    refl _ _ _ := rfl
    symm h₁ _ h₂ := by
      symm
      apply h₁
      apply h₂
    trans h₁ h₂ _ h₃ := by
      trans
      · apply h₁ h₃
      · apply h₂ h₃
  }

lemma lintegral_mul_left
    (c : ENNReal) {f : A → ENNReal} (hf : IsHom f) (μ : PreProbabilityMeasure A)
    : lintegral (fun x ↦ c * f x) μ = c * lintegral f μ := by
  rcases μ with ⟨eval, base⟩
  simp only [lintegral_mk]
  apply MeasureTheory.lintegral_const_mul
  apply hf
  simp only [QuasiBorelHom.isVar_coe]

lemma lintegral_mul_right
    (c : ENNReal) {f : A → ENNReal} (hf : IsHom f) (μ : PreProbabilityMeasure A)
    : lintegral (fun x ↦ f x * c) μ = lintegral f μ * c := by
  rcases μ with ⟨eval, base⟩
  simp only [lintegral_mk]
  apply MeasureTheory.lintegral_mul_const
  apply hf
  simp only [QuasiBorelHom.isVar_coe]

@[simp]
lemma setoid_r (μ₁ μ₂ : PreProbabilityMeasure A) : (setoid A).r μ₁ μ₂ ↔ μ₁ ≈ μ₂ := by rfl

lemma equiv_def (μ₁ μ₂ : PreProbabilityMeasure A)
    : μ₁ ≈ μ₂ ↔ (∀{f}, IsHom f → μ₁.lintegral f = μ₂.lintegral f) := by
  rfl

lemma nonempty (μ : PreProbabilityMeasure A) : Nonempty A := ⟨μ.eval 0⟩

/-- The type of variables for probability measures. -/
structure Var (A : Type*) [QuasiBorelSpace A] where
  /-- The random variable associated with each probability measure. -/
  eval : ℝ →𝒒 A
  /-- The family of base `ProbabilityMeasures`. -/
  base : ℝ → ProbabilityMeasure ℝ
  /-- The family of base measures is measurable. -/
  measurable_base : Measurable base := by fun_prop

namespace Var

attribute [fun_prop] measurable_base

/-- Evaluates a `Var`. -/
def apply : Var A → ℝ → PreProbabilityMeasure A
  | ⟨φ, μ, _⟩, r => ⟨φ, μ r⟩

@[simp]
alias apply_mk := apply.eq_1

instance : CoeFun (Var A) (fun _ ↦ ℝ → PreProbabilityMeasure A) where
  coe := apply

/-- The constant variable. -/
def const (μ : PreProbabilityMeasure A) : Var A where
  eval := μ.eval
  base _ := μ.base

@[simp]
lemma apply_const (μ : PreProbabilityMeasure A) (r : ℝ) : apply (const μ) r = μ := rfl

/-- Precomposition of variables by measurable functions. -/
def comp {f : ℝ → ℝ} (hf : Measurable f) (φ : Var A) : Var A where
  eval := φ.eval
  base r := φ.base (f r)

@[simp]
lemma apply_comp
    {f : ℝ → ℝ} (hf : Measurable f) (φ : Var A) (r : ℝ)
    : apply (comp hf φ) r = apply φ (f r) :=
  rfl

/-- Gluing of a countable number of variables. -/
noncomputable def cases
    {ix : ℝ → ℕ} (hix : Measurable ix)
    (φ : ℕ → Var A) : Var A where
  eval := {
    toFun r := (φ (unpairN r).1).eval (unpairN r).2
    property := by
      apply isHom_cases (ix := fun r ↦ (unpairN r).1) (f := fun n r ↦ (φ n).eval (unpairN r).2)
      · simp only [isHom_iff_isVar, DiscreteQuasiBorelSpace.isVar_iff_measurable]
        fun_prop
      · fun_prop
  }
  base r := ((φ (ix r)).base r).map (f := fun x ↦ pairN (ix r, x)) (by fun_prop)
  measurable_base := by
    apply measurable_cases (f := fun n r ↦
        ((φ n).base r).map (f := fun x ↦ pairN (n, x)) (by fun_prop))
    · exact hix
    · intro i
      apply Measurable.subtype_mk
      apply Measure.measurable_map'
      · fun_prop
      · apply Measurable.subtype_val
        fun_prop

lemma apply_cases
    {ix : ℝ → ℕ} (hix : Measurable ix)
    (φ : ℕ → Var A) (r : ℝ)
    : apply (cases hix φ) r ≈ φ (ix r) r := by
  simp only [cases, apply_mk, equiv_def, lintegral_mk, QuasiBorelHom.coe_mk]
  intro f hf
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [lintegral_map]
  · simp only [unpairN_pairN]
    simp only [lintegral, apply]
  · apply measurable_cases (f := fun n r ↦ f ((φ n).eval (unpairN r).2))
    · fun_prop
    · intro i
      apply Measurable.comp' (g := fun r ↦ f _) (f := fun r ↦ (unpairN r).2)
      · apply hf
        simp only [QuasiBorelHom.isVar_coe]
      · fun_prop
  · fun_prop

end Var

instance : QuasiBorelSpace (PreProbabilityMeasure A) where
  IsVar φ := ∃(ψ : Var A), ∀r, φ r ≈ ψ r
  isVar_const μ := by
    use Var.const μ
    simp only [Var.apply_const, Setoid.refl, implies_true]
  isVar_comp hf := by
    rintro ⟨μ, hμ⟩
    use Var.comp hf μ
    simp only [Var.apply_comp]
    intro r
    apply hμ
  isVar_cases' hix hφ := by
    choose φ hφ using hφ
    use Var.cases hix φ
    simp only
    intro r
    trans
    · apply hφ
    · symm
      apply Var.apply_cases

/-- The variable associated with a `PreProbabilityMeasure` variable. -/
noncomputable def subeval (φ : ℝ → PreProbabilityMeasure A) : ℝ →𝒒 A :=
  open Classical in
  if hφ : IsVar φ
  then (Classical.choose hφ).eval
  else .mk fun _ ↦ Classical.choice ((φ 0).nonempty)

/-- The measure associated with a `PreProbabilityMeasure` variable. -/
noncomputable def subbase (φ : ℝ → PreProbabilityMeasure A) : ℝ → ProbabilityMeasure ℝ :=
  open Classical in
  if hφ : IsVar φ
  then (Classical.choose hφ).base
  else fun _ ↦ default

@[simp, fun_prop, measurability]
lemma measurable_subbase (φ : ℝ → PreProbabilityMeasure A) : Measurable (subbase φ) := by
  by_cases hφ : IsVar φ
  · simp only [subbase, hφ, ↓reduceDIte]
    apply (Classical.choose hφ).measurable_base
  · simp only [subbase, hφ, ↓reduceDIte, measurable_const]

lemma sub_eq
    {φ : ℝ → PreProbabilityMeasure A} (hφ : IsVar φ)
    : ∀r, φ r ≈ .mk (subeval φ) (subbase φ r) := by
  simp only [subeval, hφ, ↓reduceDIte, subbase]
  exact Classical.choose_spec hφ

@[fun_prop]
lemma isHom_lintegral
    {k : A → B → ENNReal} (hk : IsHom fun (x, y) ↦ k x y)
    {f : A → PreProbabilityMeasure B} (hf : IsHom f)
    : IsHom (fun x ↦ lintegral (k x) (f x)) := by
  intro φ hφ
  simp only [ENNReal.IsVar_def, lintegral]
  have {r} := sub_eq (hf hφ) r (f := k (φ r)) (by fun_prop)
  simp only [lintegral] at this
  simp only [this]
  let κ : ProbabilityTheory.Kernel ℝ ℝ := {
    toFun x := ↑(subbase (fun x ↦ f (φ x)) x)
    measurable' := by
      apply Measurable.subtype_val
      fun_prop
  }
  have : ProbabilityTheory.IsFiniteKernel κ := by
    constructor
    use 1
    simp only [
      ENNReal.one_lt_top, ProbabilityTheory.Kernel.coe_mk,
      measure_univ, le_refl, implies_true, and_self, κ]
  change Measurable fun x ↦ ∫⁻ x, _ ∂κ x
  apply Measurable.lintegral_kernel_prod_left
  unfold Function.uncurry
  dsimp only

  specialize hk
    (φ := fun r ↦ (φ (unpairR r).2, ((subeval fun x ↦ f (φ x)) (unpairR r).1)))
    (by rw [←isHom_iff_isVar] at ⊢ hφ
        fun_prop)
  dsimp at hk
  have := Measurable.comp' hk (by fun_prop : Measurable pairR)
  simp only [unpairR_pairR] at this
  exact this

@[gcongr]
lemma lintegral_congr
    {k : A → ENNReal} (hk : IsHom k)
    {μ₁ μ₂ : PreProbabilityMeasure A} (hμ : μ₁ ≈ μ₂)
    : lintegral k μ₁ = lintegral k μ₂ := by
  apply hμ hk

@[gcongr]
lemma isVar_congr {f g : ℝ → PreProbabilityMeasure A} (h : ∀ x, f x ≈ g x) : IsVar f ↔ IsVar g := by
  apply Iff.intro <;>
  · intro ⟨φ, hφ⟩
    use φ
    intro r
    grw [←hφ, h]

@[gcongr]
lemma isHom_congr {f g : A → PreProbabilityMeasure B} (h : ∀ x, f x ≈ g x) : IsHom f ↔ IsHom g := by
  apply Iff.intro <;>
  · intro hf φ hφ
    rw [isVar_congr]
    · exact hf hφ
    · intro r
      grw [h]

/-- The unit operation, a.k.a. the dirac measure. -/
noncomputable def unit (x : A) : PreProbabilityMeasure A where
  eval := .mk (fun _ ↦ x)
  base := default

@[simp]
lemma lintegral_unit (f : A → ENNReal) (x : A) : lintegral f (unit x) = f x := by
  simp only [unit, lintegral_mk, QuasiBorelHom.coe_mk, lintegral_const, measure_univ, mul_one]

namespace Var

/-- The dirac measure, lifted to variables. -/
noncomputable def unit {φ : ℝ → A} (hφ : IsVar φ) : Var A where
  eval := .mk φ (by simp only [isHom_iff_isVar, hφ])
  base := diracProba
  measurable_base := by
    apply Measurable.subtype_mk
    fun_prop

@[simp]
lemma apply_unit
    {φ : ℝ → A} (hφ : IsVar φ) (r : ℝ)
    : apply (unit hφ) r ≈ PreProbabilityMeasure.unit (φ r) := by
  intro ψ hψ
  simp only [unit, apply_mk, diracProba, lintegral_mk, ProbabilityMeasure.coe_mk,
    QuasiBorelHom.coe_mk, lintegral_dirac, lintegral_unit]

end Var

@[fun_prop]
lemma isHom_unit : IsHom (unit (A := A)) := by
  intro φ hφ
  use Var.unit hφ
  intro r
  symm
  simp only [Var.apply_unit]

/-- The monadic bind operation for probability measures. -/
noncomputable def bind
    (f : A → PreProbabilityMeasure B) (μ : PreProbabilityMeasure A)
    : PreProbabilityMeasure B where
  eval := subeval (f ∘ μ.eval)
  base := ProbabilityMeasure.bind μ.base (subbase (f ∘ μ.eval))

lemma lintegral_bind
    {f : B → ENNReal} (hf : IsHom f)
    {g : A → PreProbabilityMeasure B} (hg : IsHom g)
    (μ : PreProbabilityMeasure A)
    : lintegral f (bind g μ) = lintegral (fun x ↦ lintegral f (g x)) μ := by
  simp only [lintegral, bind]
  rw [ProbabilityMeasure.lintegral_bind]
  · have : IsVar (g ∘ μ.eval) := by
      apply hg
      simp only [QuasiBorelHom.isVar_coe]
    congr 1
    ext r
    replace := sub_eq this r hf
    simp only [lintegral, Function.comp_apply] at this
    rw [this]
  · fun_prop
  · apply hf
    simp only [QuasiBorelHom.isVar_coe]

@[gcongr]
lemma bind_congr
    {f : A → PreProbabilityMeasure B} (hf : IsHom f)
    {g : A → PreProbabilityMeasure B} (hg : IsHom g)
    (h₁ : ∀ x, f x ≈ g x)
    {μ ν : PreProbabilityMeasure A} (h₂ : μ ≈ ν)
    : bind f μ ≈ bind g ν := by
  intro k hk
  rw [lintegral_bind, lintegral_bind]
  · trans
    · apply h₂
      fun_prop
    · congr
      ext x
      apply h₁ x hk
  · exact hk
  · exact hg
  · exact hk
  · exact hf

namespace Var

/-- The monadic bind, lifted to variables. -/
noncomputable def bind (f : A → PreProbabilityMeasure B) (φ : Var A) : Var B where
  eval := subeval fun x ↦ f (φ.eval x)
  base := fun r ↦ (φ.base r).bind (subbase fun x ↦ f (φ.eval x))

lemma apply_bind {f : A → PreProbabilityMeasure B} (hf : IsHom f) (φ : Var A) (r : ℝ)
    : apply (bind f φ) r ≈ PreProbabilityMeasure.bind f (φ r) := by
  intro k hk
  simp only [bind, apply_mk, lintegral_mk]
  rw [lintegral_bind, ProbabilityMeasure.lintegral_bind]
  · congr 1
    ext x
    have : IsVar (fun x ↦ f (φ.eval x)) := by
      apply hf
      simp only [QuasiBorelHom.isVar_coe]
    simp only [sub_eq this x hk, lintegral_mk]
  · fun_prop
  · apply hk
    simp only [QuasiBorelHom.isVar_coe]
  · fun_prop
  · fun_prop

end Var

@[fun_prop]
lemma isHom_bind {f : A → PreProbabilityMeasure B} (hf : IsHom f) : IsHom (bind f) := by
  intro φ ⟨ψ, hψ⟩
  use Var.bind f ψ
  intro r
  dsimp only
  grw [Var.apply_bind, hψ]
  · fun_prop
  · fun_prop
  · fun_prop

/-- The functorial `str`ength operation. -/
def str (x : A) (μ : PreProbabilityMeasure B) : PreProbabilityMeasure (A × B) where
  eval := .mk fun r ↦ (x, μ.eval r)
  base := μ.base

@[simp]
lemma lintegral_str
    (k : A × B → ENNReal)
    (x : A) (μ : PreProbabilityMeasure B)
    : lintegral k (str x μ) = lintegral (fun y ↦ k (x, y)) μ := by
  simp only [lintegral, str, QuasiBorelHom.coe_mk]

@[gcongr]
lemma str_congr (x : A) {μ₁ μ₂ : PreProbabilityMeasure B} (hμ : μ₁ ≈ μ₂) : str x μ₁ ≈ str x μ₂ := by
  intro k hk
  simp only [lintegral_str]
  apply hμ
  fun_prop

namespace Var

/-- The functorial `str`ength operation, lifted to variables. -/
noncomputable def str {φ : ℝ → A} (hφ : IsHom φ) (ψ : Var B) : Var (A × B) where
  eval := .mk fun r ↦ (φ (unpairR r).1, ψ.eval (unpairR r).2)
  base r := (ψ r).base.map (f := fun x ↦ pairR (r, x)) (by fun_prop)
  measurable_base := by
    apply Measurable.subtype_mk
    apply Measure.measurable_map'
    · fun_prop
    · apply Measurable.subtype_val
      fun_prop

lemma apply_str
    {φ : ℝ → A} (hφ : IsHom φ) (ψ : Var B) (r : ℝ)
    : apply (str hφ ψ) r ≈ PreProbabilityMeasure.str (φ r) (ψ r) := by
  intro χ hχ
  simp only [
    str, apply_mk, lintegral_mk, ProbabilityMeasure.toMeasure_map,
    QuasiBorelHom.coe_mk, lintegral_str]
  rw [MeasureTheory.lintegral_map]
  · rcases ψ
    simp only [apply_mk, unpairR_pairR, lintegral_mk]
  · apply hχ
    simp only [Prod.IsVar_def]
    apply And.intro
    · apply hφ
      simp only [Real.IsVar_def]
      fun_prop
    · apply ψ.eval.isHom_coe
      simp only [Real.IsVar_def]
      fun_prop
  · fun_prop

end Var

@[fun_prop, simp]
lemma isHom_str : IsHom (fun x : A × PreProbabilityMeasure B ↦ str x.1 x.2) := by
  intro φ ⟨hφ, ψ, hψ⟩
  have : IsHom (fun x ↦ (φ x).1) := by simp only [isHom_iff_isVar, hφ]
  use Var.str this ψ
  intro r
  dsimp only at ⊢ hψ
  grw [Var.apply_str, hψ]

noncomputable def coin (p : I) : PreProbabilityMeasure Bool where
  eval := {
    toFun := fun r ↦ r = 0
    property := by
      apply Bool.isHom_decide
      change IsHom fun x ↦ x ∈ ({0} : Set ℝ)
      simp only [
        isHom_iff_isVar, DiscreteQuasiBorelSpace.isVar_iff_measurable,
        measurable_mem, MeasurableSet.singleton]
  }
  base := {
    val :=
      ENNReal.ofReal p • Measure.dirac 0 +
      ENNReal.ofReal (σ p) • Measure.dirac 1
    property := by
      constructor
      rcases p with ⟨p, hp⟩
      simp only [Set.mem_Icc] at hp
      simp only [unitInterval.coe_symm_eq, hp, ENNReal.ofReal_sub, ENNReal.ofReal_one,
        Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ, smul_eq_mul,
        mul_one, ENNReal.ofReal_le_one, add_tsub_cancel_of_le]
  }

@[simp]
lemma lintegral_coin
    (k : Bool → ENNReal) (p : I)
    : lintegral k (coin p) = ENNReal.ofReal p * k true + ENNReal.ofReal (1 - p) * k false := by
  simp only [coin, unitInterval.coe_symm_eq, lintegral_mk, ProbabilityMeasure.coe_mk,
    QuasiBorelHom.coe_mk, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac,
    decide_true, smul_eq_mul, one_ne_zero, decide_false]

end QuasiBorelSpace.PreProbabilityMeasure
