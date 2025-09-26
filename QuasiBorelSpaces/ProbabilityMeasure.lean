import QuasiBorelSpaces.PreProbabilityMeasure
import QuasiBorelSpaces.ENNReal

open MeasureTheory
open scoped unitInterval

namespace QuasiBorelSpace

variable {A B C A' B' C' : Type*}
  [QuasiBorelSpace A] [QuasiBorelSpace B] [QuasiBorelSpace C]
  [QuasiBorelSpace A'] [QuasiBorelSpace B'] [QuasiBorelSpace C']

/-- The type of _(quasi-borel) probability measures_. -/
structure ProbabilityMeasure (A : Type*) [QuasiBorelSpace A] where
  private fromQuotient ::
  private val : Quotient (PreProbabilityMeasure.setoid A)

namespace ProbabilityMeasure

/-- Constructs a `ProbabilityMeasure` from a `PreProbabilityMeasure`. -/
def mk (μ : PreProbabilityMeasure A) : ProbabilityMeasure A := ⟨⟦μ⟧⟩

@[simp]
lemma mk_eq_iff (μ ν : PreProbabilityMeasure A) : mk μ = mk ν ↔ μ ≈ ν := by
  simp only [mk, fromQuotient.injEq, Quotient.eq, PreProbabilityMeasure.setoid_r]

@[induction_eliminator, cases_eliminator]
lemma inductionOn
    {motive : ProbabilityMeasure A → Prop} (μ : ProbabilityMeasure A)
    (mk : (μ : PreProbabilityMeasure A) → motive (mk μ))
    : motive μ := by
  rcases μ with ⟨μ⟩
  induction μ using Quotient.inductionOn with | h μ =>
  rcases μ with ⟨α, hα, μ⟩
  apply mk

/-- The integral of a function over a `ProbabilityMeasure`. -/
noncomputable def lintegral (k : A → ENNReal) (μ : ProbabilityMeasure A) : ENNReal :=
  open Classical in
  if hk : IsHom k then
    μ.val.liftOn' (PreProbabilityMeasure.lintegral k) (fun _ _ h ↦ by
      apply h
      apply hk)
  else
    0

open Classical in
@[simp]
lemma lintegral_mk
    (k : A → ENNReal) (μ : PreProbabilityMeasure A)
    : lintegral k (mk μ)
    = if IsHom k then μ.lintegral k else 0 := by
  rfl

@[ext]
lemma ext
    {μ₁ μ₂ : ProbabilityMeasure A}
    (hμ : ∀ {k}, IsHom k → μ₁.lintegral k = μ₂.lintegral k)
    : μ₁ = μ₂ := by
  cases μ₁ with | mk μ =>
  cases μ₂ with | mk ν =>
  simp only [mk_eq_iff, PreProbabilityMeasure.equiv_def]
  intro k hk
  specialize hμ hk
  simp only [lintegral_mk, hk, ↓reduceIte] at hμ
  exact hμ

/--
Converts a `ProbabilityMeasure` to the underlying `PreProbabilityMeasure`. This
may or may not be the one passed to `mk`, but will always be equivalent
(`(mk μ).toPreDist ≈ μ`).
-/
noncomputable def toPreDist (μ : ProbabilityMeasure A) : PreProbabilityMeasure A := μ.val.out

instance : QuasiBorelSpace (ProbabilityMeasure A) := lift toPreDist

lemma toPreDist_mk (μ : PreProbabilityMeasure A) : toPreDist (mk μ) ≈ μ := by
  apply Quotient.exact
  simp only [toPreDist, mk, Quotient.out_eq]

@[simp, fun_prop]
lemma isHom_toPreDist : IsHom (toPreDist (A := A)) := by
  apply isHom_of_lift

@[simp, fun_prop]
lemma isHom_mk : IsHom (mk (A := A)) := by
  rw [isHom_to_lift, PreProbabilityMeasure.isHom_congr toPreDist_mk]
  fun_prop

@[simp]
lemma lintegral_toPredist
    (μ : ProbabilityMeasure A) {k : A → ENNReal} (hk : IsHom k)
    : μ.toPreDist.lintegral k = μ.lintegral k := by
  cases μ with | mk μ =>
  simp only [lintegral_mk, hk, ↓reduceIte]
  apply toPreDist_mk μ hk

@[fun_prop]
lemma isHom_lintegral
    {k : A → B → ENNReal} (hk : IsHom fun (x, y) ↦ k x y)
    {f : A → ProbabilityMeasure B} (hf : IsHom f)
    : IsHom (fun x ↦ lintegral (k x) (f x)) := by
  have hk' {x} : IsHom (k x) := by fun_prop
  have {x} : lintegral (k x) (f x) = PreProbabilityMeasure.lintegral (k x) (f x).toPreDist := by
    simp only [hk', lintegral_toPredist]
  simp only [this]
  fun_prop

lemma lintegral_add
    {f : A → ENNReal} (hf : IsHom f)
    {g : A → ENNReal} (hg : IsHom g)
    (μ : ProbabilityMeasure A)
    : lintegral (f + g) μ = lintegral f μ + lintegral g μ := by
  cases μ with | mk μ =>
  simp only [lintegral_mk]
  have : IsHom (f + g) := by
    change IsHom (fun x ↦ f x + g x)
    fun_prop
  simp only [hf, ↓reduceIte, hg, this]
  apply PreProbabilityMeasure.lintegral_add_left
  exact hf

lemma lintegral_add'
    {f : A → ENNReal} (hf : IsHom f)
    {g : A → ENNReal} (hg : IsHom g)
    (μ : ProbabilityMeasure A)
    : lintegral (fun x ↦ f x + g x) μ = lintegral f μ + lintegral g μ := by
  apply lintegral_add hf hg

lemma lintegral_mul_left
    (c : ENNReal) {f : A → ENNReal} (hf : IsHom f) (μ : ProbabilityMeasure A)
    : lintegral (fun x ↦ c * f x) μ = c * lintegral f μ := by
  cases μ with | mk μ =>
  have : IsHom fun x ↦ c * f x := by fun_prop
  simp only [lintegral_mk, this, ↓reduceIte, hf]
  simp  (disch := fun_prop) only [PreProbabilityMeasure.lintegral_mul_left]

lemma lintegral_mul_right
    (c : ENNReal) {f : A → ENNReal} (hf : IsHom f) (μ : ProbabilityMeasure A)
    : lintegral (fun x ↦ f x * c) μ = lintegral f μ * c := by
  cases μ with | mk μ =>
  have : IsHom fun x ↦ f x * c := by fun_prop
  simp only [lintegral_mk, this, ↓reduceIte, hf]
  simp (disch := fun_prop) only [PreProbabilityMeasure.lintegral_mul_right]

/-- The monadic `unit` operation. -/
noncomputable def unit (x : A) : ProbabilityMeasure A := mk (PreProbabilityMeasure.unit x)

@[simp, fun_prop]
lemma isHom_unit : IsHom (unit (A := A)) := by
  unfold unit
  fun_prop

@[simp]
lemma lintegral_unit {k : A → ENNReal} (hk : IsHom k) (x : A) : lintegral k (unit x) = k x := by
  simp only [unit, lintegral_mk, hk, ↓reduceIte, PreProbabilityMeasure.lintegral_unit]

/-- The monadic `bind` operation. -/
noncomputable def bind
    (f : A → ProbabilityMeasure B) (μ : ProbabilityMeasure A)
    : ProbabilityMeasure B :=
  mk (PreProbabilityMeasure.bind (fun x ↦ (f x).toPreDist) μ.toPreDist)

@[simp, fun_prop]
lemma isHom_bind {f : A → ProbabilityMeasure B} (hf : IsHom f) : IsHom (bind f) := by
  unfold bind
  fun_prop

@[simp]
lemma lintegral_bind
    {k : B → ENNReal} (hk : IsHom k)
    {f : A → ProbabilityMeasure B} (hf : IsHom f)
    (μ : ProbabilityMeasure A)
    : lintegral k (bind f μ) = lintegral (fun x ↦ lintegral k (f x)) μ := by
  cases μ with | mk μ =>
  have : IsHom fun x ↦ lintegral k (f x) := by fun_prop
  simp only [bind, lintegral_mk, hk, ↓reduceIte, this]
  rw [PreProbabilityMeasure.lintegral_bind]
  · trans μ.lintegral (fun x ↦ (f x).toPreDist.lintegral k)
    · apply toPreDist_mk
      fun_prop
    · congr
      ext x
      cases f x with | mk ν =>
      simp only [hk, lintegral_toPredist, lintegral_mk, ↓reduceIte]
  · fun_prop
  · fun_prop

@[simp]
lemma bind_unit {f : A → ProbabilityMeasure B} (hf : IsHom f) (x : A) : bind f (unit x) = f x := by
  ext k hk
  simp (disch := fun_prop) only [lintegral_bind, lintegral_unit]

@[simp]
lemma unit_bind (μ : ProbabilityMeasure A) : bind unit μ = μ := by
  ext k hk
  simp (disch := fun_prop) only [lintegral_bind, lintegral_unit]

@[simp]
lemma bind_bind
    {f : B → ProbabilityMeasure C} (hf : IsHom f)
    {g : A → ProbabilityMeasure B} (hg : IsHom g)
    (μ : ProbabilityMeasure A)
    : bind f (bind g μ) = bind (fun x ↦ bind f (g x)) μ := by
  ext k hk
  simp (disch := fun_prop) only [lintegral_bind]

/-- The functorial `map` operation. -/
noncomputable def map (f : A → B) (μ : ProbabilityMeasure A) : ProbabilityMeasure B :=
  bind (fun x ↦ unit (f x)) μ

@[fun_prop]
lemma isHom_map {f : A → B} (hf : IsHom f) : IsHom (map f) := by
  unfold map
  fun_prop

@[simp]
lemma lintegral_map
    {k : B → ENNReal} (hk : IsHom k)
    {f : A → B} (hf : IsHom f) (μ : ProbabilityMeasure A)
    : lintegral k (map f μ) = lintegral (fun x ↦ k (f x)) μ := by
  simp (disch := fun_prop) only [map, lintegral_bind, lintegral_unit]

@[simp]
lemma map_id : map (fun x : A ↦ x) = id := by
  funext μ
  simp only [map, unit_bind, id_eq]

@[simp]
lemma map_id' : map (A := A) id = id := map_id

@[simp]
lemma map_map
    {f : B → C} (hf : IsHom f)
    {g : A → B} (hg : IsHom g)
    (μ : ProbabilityMeasure A)
    : map f (map g μ) = map (fun x ↦ f (g x)) μ := by
  simp (disch := fun_prop) only [map, bind_bind, bind_unit]

@[simp]
lemma map_bind
    {f : B → C} (hf : IsHom f)
    {g : A → ProbabilityMeasure B} (hg : IsHom g)
    (μ : ProbabilityMeasure A)
    : map f (bind g μ) = bind (fun x ↦ map f (g x)) μ := by
  simp (disch := fun_prop) only [map, bind_bind]

@[simp]
lemma bind_map
    {f : B → ProbabilityMeasure C} (hf : IsHom f)
    {g : A → B} (hg : IsHom g)
    (μ : ProbabilityMeasure A)
    : bind f (map g μ) = bind (fun x ↦ f (g x)) μ := by
  simp (disch := fun_prop) only [map, bind_bind, bind_unit]

@[simp]
lemma map_unit {f : A → B} (hf : IsHom f) (x : A) : map f (unit x) = unit (f x) := by
  simp (disch := fun_prop) only [map, bind_unit]

@[simp]
lemma bind_unit_eq_map {f : A → B} : bind (fun x ↦ unit (f x)) = map f := by
  funext μ
  simp only [map]

/-- The functorial `str`ength operation. -/
noncomputable def str (x : A) (μ : ProbabilityMeasure B) : ProbabilityMeasure (A × B) :=
  mk (PreProbabilityMeasure.str x μ.toPreDist)

@[simp]
lemma lintegral_str
    {k : A × B → ENNReal} (hk : IsHom k)
    (x : A) (μ : ProbabilityMeasure B)
    : lintegral k (str x μ) = lintegral (fun y ↦ k (x, y)) μ := by
  cases μ with | mk μ =>
  have : IsHom fun y ↦ k (x, y) := by fun_prop
  simp only [
    str, lintegral_mk, hk, ↓reduceIte, PreProbabilityMeasure.lintegral_str,
    this, lintegral_toPredist]

@[simp, local fun_prop]
lemma isHom_str : IsHom (Function.uncurry (str (A := A) (B := B))) := by
  unfold Function.uncurry
  simp only [str]
  fun_prop

@[fun_prop]
lemma isHom_str'
    {f : A → B} (hf : IsHom f)
    {g : A → ProbabilityMeasure C} (hg : IsHom g)
    : IsHom (fun x ↦ str (f x) (g x)) := by
  fun_prop

@[simp]
lemma str_eq_map (x : A) (μ : ProbabilityMeasure B) : str x μ = map (x, ·) μ := by
  ext k hk
  simp (disch := fun_prop) only [lintegral_str, lintegral_map]

@[fun_prop]
lemma isHom_bind'
    {f : C → A → ProbabilityMeasure B} (hf : IsHom (Function.uncurry f))
    {g : C → ProbabilityMeasure A} (hg : IsHom g)
    : IsHom (fun x ↦ bind (f x) (g x)) := by
  have hf' : ∀x, IsHom (f x) := by fun_prop
  have {x}
      : bind (f x) (g x)
      = bind (fun x : (A →𝒒 ProbabilityMeasure B) × A ↦ x.1 x.2) (str ⟨f x, hf' x⟩ (g x)) := by
    simp only [
      str_eq_map, QuasiBorelHom.isHom_eval, Prod.isHom_iff, isHom_const,
      isHom_id', and_self, bind_map, QuasiBorelHom.coe_mk]
  simp only [this]
  fun_prop

@[fun_prop]
lemma isHom_map'
    {f : C → A → B} (hf : IsHom (Function.uncurry f))
    {g : C → ProbabilityMeasure A} (hg : IsHom g)
    : IsHom (fun x ↦ map (f x) (g x)) := by
  unfold map
  fun_prop

example (μ : ProbabilityMeasure A) : str () μ = map ((), ·) μ := by
  simp only [str_eq_map]

example (x : A) (y : B) : str x (unit y) = unit (x, y) := by
  simp only [str_eq_map, Prod.isHom_iff, isHom_const, isHom_id', and_self, map_unit]

example
    {f : A → A'} (hf : IsHom f)
    {g : B → B'} (hg : IsHom g)
    (x : A) (μ : ProbabilityMeasure B)
    : map (Prod.map f g) (str x μ) = str (f x) (map g μ) := by
  simp (disch := fun_prop) only [str_eq_map, map_map, Prod.map_apply]

example
    (x : A) (μ : ProbabilityMeasure (ProbabilityMeasure B))
    : bind (Function.uncurry str) (str x μ) = str x (bind id μ) := by
  simp only [
    str_eq_map, isHom_str, Prod.isHom_iff, isHom_const, isHom_id', and_self,
    bind_map, Function.uncurry_apply_pair, isHom_id, map_bind, id_eq]

/-- The Bernoulli measure. -/
noncomputable def coin (p : I) : ProbabilityMeasure Bool :=
  mk (.coin p)

@[simp]
lemma lintegral_coin
    (k : Bool → ENNReal) (p : I)
    : lintegral k (coin p) = ENNReal.ofReal p * k true + ENNReal.ofReal (1 - p) * k false := by
  simp only [
    coin, lintegral_mk, isHom_of_discrete_countable,
    ↓reduceIte, PreProbabilityMeasure.lintegral_coin]

/-- Probabilistic choice. -/
noncomputable def choose (p : I) (μ ν : ProbabilityMeasure A) : ProbabilityMeasure A :=
  bind (fun b ↦ if b then μ else ν) (coin p)

@[fun_prop]
lemma isHom_choose
    (p : I)
    {f : A → ProbabilityMeasure B} (hf : IsHom f)
    {g : A → ProbabilityMeasure B} (hg : IsHom g)
    : IsHom (fun x ↦ choose p (f x) (g x)) := by
  simp only [choose]
  apply isHom_bind'
  · unfold Function.uncurry
    dsimp only
    apply isHom_cases (ix := Prod.snd) (f := fun (b : Bool) x ↦ if b then f x.1 else g x.1)
    · fun_prop
    · intro b
      cases b <;>
      · simp only [Bool.false_eq_true, ↓reduceIte]
        fun_prop
  · fun_prop

@[simp]
lemma lintegral_choose
    {k : A → ENNReal} (hk : IsHom k)
    (p : I) (μ ν : ProbabilityMeasure A)
    : lintegral k (choose p μ ν)
    = ENNReal.ofReal p * lintegral k μ + ENNReal.ofReal (σ p) * lintegral k ν := by
  simp (disch := fun_prop) only [choose, unitInterval.coe_symm_eq]
  rw [lintegral_bind, lintegral_coin]
  · simp only [↓reduceIte, Bool.false_eq_true]
  · fun_prop
  · apply isHom_cases (f := fun (p : Bool) _ ↦ if p then μ else ν)
    · fun_prop
    · fun_prop

@[simp]
lemma choose_one (μ ν : ProbabilityMeasure A) : choose 1 μ ν = μ := by
  ext k hk
  simp (disch := fun_prop) only [lintegral_choose, Set.Icc.coe_one, ENNReal.ofReal_one, one_mul,
    unitInterval.symm_one, Set.Icc.coe_zero, ENNReal.ofReal_zero, zero_mul, add_zero]

@[simp]
lemma choose_zero (μ ν : ProbabilityMeasure A) : choose 0 μ ν = ν := by
  ext k hk
  simp (disch := fun_prop) only [lintegral_choose, Set.Icc.coe_zero, ENNReal.ofReal_zero, zero_mul,
    unitInterval.symm_zero, Set.Icc.coe_one, ENNReal.ofReal_one, one_mul, zero_add]

@[simp]
lemma choose_eq (p : I) (μ : ProbabilityMeasure A) : choose p μ μ = μ := by
  rcases p with ⟨p, hp⟩
  simp only [Set.mem_Icc] at hp
  ext k hk
  simp (disch := fun_prop) [lintegral_choose, unitInterval.coe_symm_eq]
  simp only [hp, ENNReal.ofReal_sub, ENNReal.ofReal_one]

  wlog hkμ : lintegral k μ ≠ ⊤
  · simp only [ne_eq, Decidable.not_not] at hkμ
    simp only [hkμ, ENNReal.add_eq_top]
    by_cases h : p > 0
    · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, h, ENNReal.mul_top, true_or]
    · have : p = 0 := by grind
      subst this
      simp only [ENNReal.ofReal_zero, zero_mul, ENNReal.zero_ne_top, tsub_zero, one_mul, or_true]

  rw [ENNReal.sub_mul]
  · simp only [one_mul]
    apply add_tsub_cancel_of_le
    apply mul_le_of_le_one_left'
    simp only [ENNReal.ofReal_le_one, hp]
  · simp only [ne_eq, hkμ, not_false_eq_true, implies_true]

lemma choose_comm (p : I) (μ ν : ProbabilityMeasure A) : choose p μ ν = choose (σ p) ν μ := by
  ext k hk
  simp (disch := fun_prop) only [lintegral_choose, unitInterval.coe_symm_eq, unitInterval.symm_symm]
  rw [add_comm]

private lemma choose_assoc_bound {p q : I}
    (hp₁ : 0 < p) (hp₂ : p < 1)
    (hq₁ : 0 < q) (hq₂ : q < 1)
    : (σ p * q : ℝ) / σ (p * q) ∈ I := by
  have ⟨hq₃, hq₄⟩ := q.property
  have ⟨hp₃, hp₄⟩ := p.property
  simp only [unitInterval.coe_symm_eq, Set.mem_Icc] at ⊢ hp₃ hp₄ hq₃ hq₄
  apply And.intro
  · apply div_nonneg
    · rw [mul_nonneg_iff_left_nonneg_of_pos]
      · simp only [sub_nonneg]
        assumption
      · assumption
    · grind
  · rw [div_le_iff₀]
    · simp only [Set.Icc.coe_mul, one_mul]
      rw [sub_mul]
      apply sub_le_sub
      · simp only [one_mul]
        assumption
      · rfl
    · simp only [Set.Icc.coe_mul, sub_pos]
      sorry

lemma choose_assoc {p q} {μ₁ μ₂ μ₃ : ProbabilityMeasure A}
    (hp₁ : 0 < p) (hp₂ : p < 1)
    (hq₁ : 0 < q) (hq₂ : q < 1)
    : choose q (choose p μ₁ μ₂) μ₃
    = choose (p * q) μ₁ (choose ⟨_, choose_assoc_bound hp₁ hp₂ hq₁ hq₂⟩ μ₂ μ₃) := by
  sorry

@[simp]
lemma bind_choose
    {f : A → ProbabilityMeasure B} (hf : IsHom f)
    (p : unitInterval) (μ ν : ProbabilityMeasure A)
    : bind f (choose p μ ν) = choose p (bind f μ) (bind f ν) := by
  ext k hk
  simp (disch := fun_prop) only [lintegral_bind, lintegral_choose, unitInterval.coe_symm_eq]

@[simp]
lemma map_choose
    {f : A → B} (hf : IsHom f)
    (p : unitInterval) (μ ν : ProbabilityMeasure A)
    : map f (choose p μ ν) = choose p (map f μ) (map f ν) := by
  apply bind_choose
  fun_prop

@[simp]
lemma choose_bind
    {f : A → ProbabilityMeasure B} (hf : IsHom f)
    {g : A → ProbabilityMeasure B} (hg : IsHom g)
    (p : unitInterval) (μ : ProbabilityMeasure A)
    : bind (fun x ↦ choose p (f x) (g x)) μ = choose p (bind f μ) (bind g μ) := by
  ext k hk
  simp (disch := fun_prop) only [
    lintegral_bind, lintegral_choose, unitInterval.coe_symm_eq,
    lintegral_add', lintegral_mul_left]

end QuasiBorelSpace.ProbabilityMeasure
