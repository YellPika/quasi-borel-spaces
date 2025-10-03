import QuasiBorelSpaces.ENNReal
import QuasiBorelSpaces.PreProbabilityMeasure
import QuasiBorelSpaces.SeparatesPoints

open MeasureTheory
open scoped unitInterval

namespace QuasiBorelSpace

variable {A B C A' B' C' : Type*}
  [QuasiBorelSpace A] [QuasiBorelSpace B] [QuasiBorelSpace C]
  [QuasiBorelSpace A'] [QuasiBorelSpace B'] [QuasiBorelSpace C']

/-! ## Basic Definitions -/

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

/--
Converts a `ProbabilityMeasure` to the underlying `PreProbabilityMeasure`. This
may or may not be the one passed to `mk`, but will always be equivalent
(`(mk μ).toPreProbabilityMeasure ≈ μ`).
-/
noncomputable def toPreProbabilityMeasure (μ : ProbabilityMeasure A)
    : PreProbabilityMeasure A :=
  μ.val.out

lemma toPreProbabilityMeasure_mk (μ : PreProbabilityMeasure A)
    : toPreProbabilityMeasure (mk μ) ≈ μ := by
  apply Quotient.exact
  simp only [toPreProbabilityMeasure, mk, Quotient.out_eq]

lemma nonempty (μ : ProbabilityMeasure A) : Nonempty A := μ.toPreProbabilityMeasure.nonempty

/-! ## `QuasiBorelSpace` Instance -/

instance : QuasiBorelSpace (ProbabilityMeasure A) := lift toPreProbabilityMeasure

@[simp, fun_prop]
lemma isHom_toPreProbabilityMeasure : IsHom (toPreProbabilityMeasure (A := A)) := by
  apply isHom_of_lift

@[simp, fun_prop]
lemma isHom_mk : IsHom (mk (A := A)) := by
  rw [isHom_to_lift, PreProbabilityMeasure.isHom_congr toPreProbabilityMeasure_mk]
  fun_prop

/-! ## Integrals -/

/-- The integral of a function over a `ProbabilityMeasure`. -/
noncomputable def lintegral (k : A → ENNReal) (μ : ProbabilityMeasure A) : ENNReal :=
  μ.toPreProbabilityMeasure.lintegral k

@[simp]
lemma lintegral_mk
    {k : A → ENNReal} (hk : IsHom k) (μ : PreProbabilityMeasure A)
    : lintegral k (mk μ) = μ.lintegral k := by
  apply PreProbabilityMeasure.lintegral_congr hk
  apply toPreProbabilityMeasure_mk

@[simp]
lemma lintegral_toPreProbabilityMeasure
    (μ : ProbabilityMeasure A) (k : A → ENNReal)
    : μ.toPreProbabilityMeasure.lintegral k = μ.lintegral k := by
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
  simp only [hk, lintegral_mk] at hμ
  exact hμ

@[fun_prop]
lemma isHom_lintegral
    {k : A → B → ENNReal} (hk : IsHom fun (x, y) ↦ k x y)
    {f : A → ProbabilityMeasure B} (hf : IsHom f)
    : IsHom (fun x ↦ lintegral (k x) (f x)) := by
  simp (disch := fun_prop) only [← lintegral_toPreProbabilityMeasure]
  fun_prop

lemma lintegral_add
    {f : A → ENNReal} (hf : IsHom f)
    {g : A → ENNReal} (hg : IsHom g)
    (μ : ProbabilityMeasure A)
    : lintegral (f + g) μ = lintegral f μ + lintegral g μ := by
  cases μ with | mk μ =>
  have : IsHom (f + g) := by
    change IsHom (fun x ↦ f x + g x)
    fun_prop
  simp (disch := fun_prop) only [lintegral_mk]
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
  simp (disch := fun_prop) only [lintegral_mk, PreProbabilityMeasure.lintegral_mul_left]

lemma lintegral_mul_right
    (c : ENNReal) {f : A → ENNReal} (hf : IsHom f) (μ : ProbabilityMeasure A)
    : lintegral (fun x ↦ f x * c) μ = lintegral f μ * c := by
  cases μ with | mk μ =>
  simp (disch := fun_prop) only [lintegral_mk, PreProbabilityMeasure.lintegral_mul_right]

@[simp]
lemma lintegral_const (c : ENNReal) (μ : ProbabilityMeasure A) : lintegral (fun _ ↦ c) μ = c := by
  cases μ with | mk μ =>
  simp (disch := fun_prop) only [lintegral_mk, PreProbabilityMeasure.lintegral_const]

@[simp]
lemma lintegral_mono
    {f g : A → ENNReal} (h : f ≤ g) (μ : ProbabilityMeasure A)
    : lintegral f μ ≤ lintegral g μ := by
  unfold lintegral
  apply PreProbabilityMeasure.lintegral_mono h

lemma lintegral_iSup
    (f : ℕ → A → ENNReal) (hf₁ : Monotone f) (hf₂ : ∀ n, IsHom (f n)) (μ : ProbabilityMeasure A)
    : ⨆n, lintegral (f n) μ = lintegral (⨆n, f n) μ := by
  unfold lintegral
  apply PreProbabilityMeasure.lintegral_iSup f hf₁ hf₂

lemma lintegral_finset_sum {A}
    (s : Finset A) {f : A → B → ENNReal}
    (hf : ∀ b ∈ s, IsHom (f b)) (μ : ProbabilityMeasure B) :
    lintegral (fun a ↦ ∑ b ∈ s, f b a) μ = ∑ b ∈ s, lintegral (f b) μ := by
  unfold lintegral
  apply PreProbabilityMeasure.lintegral_finset_sum s hf

/-! ## Measures -/

noncomputable instance : FunLike (ProbabilityMeasure A) (Set A) ENNReal where
  coe μ s := μ.toPreProbabilityMeasure.measureOf s
  coe_injective' := by
    intro μ₁ μ₂ h
    induction μ₁ with | mk μ₁ =>
    induction μ₂ with | mk μ₂ =>
    simp only [mk_eq_iff]
    rw [PreProbabilityMeasure.equiv_def']
    intro p hp
    grw [←toPreProbabilityMeasure_mk μ₁, ←toPreProbabilityMeasure_mk μ₂]
    · apply congr_fun h
    · fun_prop
    · fun_prop

instance : OuterMeasureClass (ProbabilityMeasure A) A where
  measure_empty _ := by
    simp only [DFunLike.coe, PreProbabilityMeasure.measureOf_empty]
  measure_mono _ _ _ h := by
    apply PreProbabilityMeasure.measureOf_mono _ h
  measure_iUnion_nat_le _ _ _ := by
    apply PreProbabilityMeasure.measureOf_iUnion_le

/-! ## Point Separation -/

instance : SeparatesPoints (ProbabilityMeasure A) where
  separates μ₁ μ₂ h := by
    ext k
    apply h _
    · apply isHom_comp'
      · rw [isHom_def]
        intro φ hφ
        simp only [isHom_ofMeasurableSpace] at ⊢ hφ
        have : MeasurableSet { x | x ∈ φ ⁻¹' ({lintegral k μ₁} : Set _) } := by
          apply hφ
          apply measurableSet_eq
        simp only [Set.mem_preimage, Set.mem_singleton_iff, measurableSet_setOf] at this
        grind
      · fun_prop
    · rfl

/-! ## Operations -/

/-! ### `unit` -/

/-- The monadic `unit` operation. -/
noncomputable def unit (x : A) : ProbabilityMeasure A := mk (PreProbabilityMeasure.unit x)

@[simp, fun_prop]
lemma isHom_unit : IsHom (unit (A := A)) := by
  unfold unit
  fun_prop

@[simp]
lemma lintegral_unit {k : A → ENNReal} (hk : IsHom k) (x : A) : lintegral k (unit x) = k x := by
  simp only [unit, hk, lintegral_mk, PreProbabilityMeasure.lintegral_unit]

@[simp]
lemma unit_injective [SeparatesPoints A] : Function.Injective (unit (A := A)) := by
  intro x y h
  simp only [ProbabilityMeasure.ext_iff] at h
  apply separatesPoints_def
  intro p hp hx
  classical
  have : IsHom fun x ↦ if p x then 1 else (0 : ENNReal) := by
    apply Prop.isHom_ite <;> fun_prop
  specialize h this
  simp (disch := fun_prop) only [
    lintegral_unit, hx, ↓reduceIte, left_eq_ite_iff, one_ne_zero,
    imp_false, Decidable.not_not] at h
  exact h

@[simp]
lemma unit_inj [SeparatesPoints A] (x y : A) : unit x = unit y ↔ x = y := by
  apply Iff.intro
  · apply unit_injective
  · grind

lemma separatesPoints_iff_unit_injective
    : SeparatesPoints A ↔ Function.Injective (unit (A := A)) := by
  apply Iff.intro
  · intro _
    apply unit_injective
  · intro h
    constructor
    intro x y h'
    apply h
    ext k hk
    apply h'
    · simp only [hk, lintegral_unit]
      apply isHom_comp' ?_ hk
      rw [isHom_def]
      intro φ hφ
      simp only [isHom_ofMeasurableSpace] at ⊢ hφ
      apply MeasurableSet.mem
      have : MeasurableSet fun r ↦ r ∈ (φ ⁻¹' ({k x} : Set _)) := by
        apply hφ
        apply measurableSet_eq
      grind
    · rfl

/-! ### `bind` -/

/-- The monadic `bind` operation. -/
noncomputable def bind
    (f : A → ProbabilityMeasure B) (μ : ProbabilityMeasure A)
    : ProbabilityMeasure B :=
  mk (PreProbabilityMeasure.bind (fun x ↦ (f x).toPreProbabilityMeasure) μ.toPreProbabilityMeasure)

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
  simp only [bind, hk, lintegral_mk, this]
  rw [PreProbabilityMeasure.lintegral_bind]
  · apply toPreProbabilityMeasure_mk
    fun_prop
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

/-! ### `map` -/

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

/-! ### `str` -/

/-- The functorial `str`ength operation. -/
noncomputable def str (x : A) (μ : ProbabilityMeasure B) : ProbabilityMeasure (A × B) :=
  mk (PreProbabilityMeasure.str x μ.toPreProbabilityMeasure)

@[simp]
lemma lintegral_str
    {k : A × B → ENNReal} (hk : IsHom k)
    (x : A) (μ : ProbabilityMeasure B)
    : lintegral k (str x μ) = lintegral (fun y ↦ k (x, y)) μ := by
  cases μ with | mk μ =>
  simp (disch := fun_prop) only [
    str, lintegral_mk, PreProbabilityMeasure.lintegral_str,
    lintegral_toPreProbabilityMeasure]

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

/-! ### `coin` -/

/-- The Bernoulli measure. -/
noncomputable def coin (p : I) : ProbabilityMeasure Bool :=
  mk (.coin p)

@[simp]
lemma lintegral_coin
    (k : Bool → ENNReal) (p : I)
    : lintegral k (coin p) = ENNReal.ofReal p * k true + ENNReal.ofReal (1 - p) * k false := by
  simp only [coin, isHom_of_discrete_countable, lintegral_mk, PreProbabilityMeasure.lintegral_coin]

/-! ### `choose` -/

/-- Probabilistic choice. -/
noncomputable def choose (p : I) (μ ν : ProbabilityMeasure A) : ProbabilityMeasure A :=
  bind (fun b ↦ if b then μ else ν) (coin p)

@[inherit_doc choose]
scoped notation:65 μ " ◃" p "▹ " ν:66 => choose p μ ν

@[fun_prop]
lemma isHom_choose
    (p : I)
    {f : A → ProbabilityMeasure B} (hf : IsHom f)
    {g : A → ProbabilityMeasure B} (hg : IsHom g)
    : IsHom (fun x ↦ f x ◃p▹ g x) := by
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
    : lintegral k (μ ◃p▹ ν)
    = ENNReal.ofReal p * lintegral k μ + ENNReal.ofReal (σ p) * lintegral k ν := by
  simp (disch := fun_prop) only [choose, unitInterval.coe_symm_eq]
  rw [lintegral_bind, lintegral_coin]
  · simp only [↓reduceIte, Bool.false_eq_true]
  · fun_prop
  · apply isHom_cases (f := fun (p : Bool) _ ↦ if p then μ else ν)
    · fun_prop
    · fun_prop

@[simp]
lemma choose_one (μ ν : ProbabilityMeasure A) : μ ◃ 1 ▹ ν = μ := by
  ext k hk
  simp (disch := fun_prop) only [lintegral_choose, Set.Icc.coe_one, ENNReal.ofReal_one, one_mul,
    unitInterval.symm_one, Set.Icc.coe_zero, ENNReal.ofReal_zero, zero_mul, add_zero]

@[simp]
lemma choose_zero (μ ν : ProbabilityMeasure A) : μ ◃ 0 ▹ ν = ν := by
  ext k hk
  simp (disch := fun_prop) only [lintegral_choose, Set.Icc.coe_zero, ENNReal.ofReal_zero, zero_mul,
    unitInterval.symm_zero, Set.Icc.coe_one, ENNReal.ofReal_one, one_mul, zero_add]

@[simp]
lemma choose_eq (p : I) (μ : ProbabilityMeasure A) : μ ◃p▹ μ = μ := by
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

lemma choose_comm (p : I) (μ ν : ProbabilityMeasure A) : μ ◃p▹ ν = ν ◃σ p▹ μ := by
  ext k hk
  simp (disch := fun_prop) only [lintegral_choose, unitInterval.coe_symm_eq, unitInterval.symm_symm]
  rw [add_comm]

private lemma choose_assoc_bound {p q : I}
    (hp₁ : 0 < p) (hp₂ : p < 1)
    (hq₁ : 0 < q) (hq₂ : q < 1)
    : (σ p * q : ℝ) / σ (p * q) ∈ I := by
  have hp := p.property
  have hq := q.property
  simp only [unitInterval.coe_symm_eq, Set.mem_Icc, Set.Icc.coe_mul]
  have hp_pos : 0 < (p : ℝ) := by simpa using hp₁
  have hq_pos : 0 < (q : ℝ) := by simpa using hq₁
  have hp_lt : (p : ℝ) < 1 := by simpa using hp₂
  have hq_lt : (q : ℝ) < 1 := by simpa using hq₂
  have h_denom_pos : 0 < 1 - (p : ℝ) * ↑q := by nlinarith
  constructor
  · apply div_nonneg <;> nlinarith
  · rw [div_le_one h_denom_pos]
    nlinarith

lemma choose_assoc {p q} {μ₁ μ₂ μ₃ : ProbabilityMeasure A}
    (hp₁ : 0 < p) (hp₂ : p < 1)
    (hq₁ : 0 < q) (hq₂ : q < 1)
    : (μ₁ ◃p▹ μ₂) ◃q▹ μ₃
    = μ₁ ◃p * q▹ (μ₂ ◃⟨_, choose_assoc_bound hp₁ hp₂ hq₁ hq₂⟩▹ μ₃) := by
  sorry

@[simp]
lemma bind_choose
    {f : A → ProbabilityMeasure B} (hf : IsHom f)
    (p : unitInterval) (μ ν : ProbabilityMeasure A)
    : bind f (μ ◃p▹ ν) = bind f μ ◃p▹ bind f ν := by
  ext k hk
  simp (disch := fun_prop) only [lintegral_bind, lintegral_choose, unitInterval.coe_symm_eq]

@[simp]
lemma map_choose
    {f : A → B} (hf : IsHom f)
    (p : unitInterval) (μ ν : ProbabilityMeasure A)
    : map f (μ ◃p▹ ν) = map f μ ◃p▹ map f ν := by
  apply bind_choose
  fun_prop

@[simp]
lemma choose_bind
    {f : A → ProbabilityMeasure B} (hf : IsHom f)
    {g : A → ProbabilityMeasure B} (hg : IsHom g)
    (p : unitInterval) (μ : ProbabilityMeasure A)
    : bind (fun x ↦ f x ◃p▹ g x) μ = bind f μ ◃p▹ bind g μ := by
  ext k hk
  simp (disch := fun_prop) only [
    lintegral_bind, lintegral_choose, unitInterval.coe_symm_eq,
    lintegral_add', lintegral_mul_left]

end QuasiBorelSpace.ProbabilityMeasure
