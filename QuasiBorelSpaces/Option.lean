import QuasiBorelSpaces.IsHomDiagonal
import QuasiBorelSpaces.OmegaCompletePartialOrder.Option
import QuasiBorelSpaces.Sum
import QuasiBorelSpaces.Unit

namespace QuasiBorelSpace.Option

variable {A B C : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B] [QuasiBorelSpace C]

/--
We derive the `QuasiBorelSpace` instance for `Option A`s from their encoding as
`Unit ⊕ A`.
-/
abbrev Encoding (A : Type*) := Unit ⊕ A

namespace Encoding

/-- The encoded version of `Option.none`. -/
def none : Encoding A := .inl ()

/-- The encoded version of `Option.some`. -/
def some (x : A) : Encoding A := .inr x

/-- The encoded version of `Option.elim`. -/
def elim (x : B) (f : A → B) : Encoding A → B :=
  Sum.elim (fun _ ↦ x) f

@[fun_prop, simp]
lemma isHom_some : IsHom (some (A := A)) := by
  unfold some
  fun_prop

@[fun_prop]
lemma isHom_elim
    {f : A → C} (hf : IsHom f)
    {g : A → B → C} (hg : IsHom fun (x, y) ↦ g x y)
    {h : A → Encoding B} (hh : IsHom h)
    : IsHom (fun x ↦ elim (f x) (g x) (h x)) := by
  unfold elim
  fun_prop

end Encoding

/-- Encodes an `Option A` as an `Encoding A`. -/
def encode (x : Option A) : Unit ⊕ A :=
  Option.elim x Encoding.none Encoding.some

instance : QuasiBorelSpace (Option A) := lift encode

@[fun_prop, simp]
lemma isHom_encode : IsHom (encode (A := A)) := by
  apply isHom_of_lift

@[fun_prop]
lemma isHom_some {f : A → B} (hf : IsHom f) : IsHom (fun x ↦ some (f x)) := by
  simp only [isHom_to_lift (A := Option _), encode, Option.elim_some]
  fun_prop

@[fun_prop]
lemma isHom_elim
    {f : A → Option B} (hf : IsHom f)
    {g : A → C} (hg : IsHom g)
    {h : A → B → C} (hh : IsHom fun (x, y) ↦ h x y)
    : IsHom (fun x ↦ Option.elim (f x) (g x) (h x)) := by
  have {x}
      : Option.elim (f x) (g x) (h x)
      = Encoding.elim (g x) (h x) (encode (f x)) := by
    cases f x <;> rfl
  simp only [this]
  fun_prop

@[fun_prop]
lemma isHom_map
    {f : A → B → C} (hf : IsHom fun (x, y) ↦ f x y)
    {g : A → Option B} (hg : IsHom g)
    : IsHom (fun x ↦ Option.map (f x) (g x)) := by
  have {x} : Option.map (f x) (g x) = Option.elim (g x) .none (.some ∘ f x) := by
    cases g x <;> rfl
  simp only [this]
  fun_prop

@[fun_prop]
lemma isHom_bind
    {f : A → B → Option C} (hf : IsHom fun (x, y) ↦ f x y)
    {g : A → Option B} (hg : IsHom g)
    : IsHom (fun x ↦ Option.bind (g x) (f x)) := by
  have {x} : Option.bind (g x) (f x) = Option.elim (g x) .none (f x) := by
    cases g x <;> rfl
  simp only [this]
  fun_prop

@[fun_prop]
lemma isHom_getD
    {f : A → Option B} (hf : IsHom f)
    {g : A → B} (hg : IsHom g)
    : IsHom (fun x ↦ (f x).getD (g x)) := by
  have {x} : Option.getD (f x) (g x) = Option.elim (f x) (g x) id := by
    cases f x <;> rfl
  simp only [this]
  fun_prop

@[simp, fun_prop]
lemma isHom_isSome : IsHom (fun x : Option A ↦ x.isSome) := by
  have (x : Option A) : x.isSome = x.elim false (fun _ ↦ true) := by
    cases x <;> rfl
  simp only [this]
  fun_prop

@[simp, fun_prop]
lemma isHom_isNone : IsHom (fun x : Option A ↦ x.isNone) := by
  have (x : Option A) : x.isNone = x.elim true (fun _ ↦ false) := by
    cases x <;> rfl
  simp only [this]
  fun_prop

instance [IsHomDiagonal A] : IsHomDiagonal (Option A) where
  isHom_eq := by
    have {x y : Option A}
        : x = y
        ↔ x.elim (y.elim True (fun _ ↦ False)) (fun x ↦ y.elim False (x = ·)) := by
      cases x <;> cases y <;>
        simp only [reduceCtorEq, Option.elim_none, Option.elim_some, Option.some.injEq]
    simp only [this]
    fun_prop

end QuasiBorelSpace.Option

namespace OmegaQuasiBorelSpace.Option

open QuasiBorelSpace
open OmegaCompletePartialOrder

noncomputable instance {A : Type*} [OmegaQuasiBorelSpace A] : OmegaQuasiBorelSpace (Option A) where
  isHom_ωSup' c hc := by
    classical
    change IsHom fun r ↦ ωSup _
    simp only [
      ωSup, Chain.Option.sequence_def, Chain.map_coe, Pi.evalOrderHom_coe,
      Function.comp_apply, Function.eval, Option.map_dif]
    apply Prop.isHom_dite
    · fun_prop
    · apply Option.isHom_some
      rw [isHom_def]
      intro φ hφ
      classical
      have : Nonempty A := ⟨Option.get _ (Nat.find_spec (φ 0).property)⟩
      let c' : Chain (ℝ → A) := {
        toFun n r := Chain.Option.project
          (c.map (Pi.evalOrderHom (φ r).val))
          (by obtain ⟨q, hq⟩ := φ r
              simp only [
                Chain.map_coe, Pi.evalOrderHom_coe,
                Function.comp_apply, Function.eval, hq])
          n
        monotone' i j h r := by
          apply (Chain.Option.project _ _).monotone
          exact h
      }
      apply isHom_ωSup c' fun n ↦ ?_
      simp only [
        Chain, Chain.map, Chain.Option.project_def, OrderHom.comp_coe,
        Pi.evalOrderHom_coe, Function.comp_apply, Function.eval, OrderHom.coe_mk, c']
      apply Option.isHom_getD
      · apply isHom_cases (f := fun i x ↦ c (i + n) (φ x))
        · rw [isHom_iff_measurable]
          intro X hX
          have : (fun x ↦ Nat.find (φ x).property) ⁻¹' X
                = {r | ∃n ∈ X, (c n (φ r)).isSome ∧ ∀m < n, (c m (φ r)).isNone} := by
            ext r
            simp only [Set.mem_preimage, Set.mem_setOf_eq]
            apply Iff.intro
            · intro h
              use Nat.find (φ r).property, h
              simp only [Option.isSome_iff_exists, Option.isNone_iff_eq_none]
              have hφ := Nat.find_spec (φ r).property
              simp only [Option.isSome_iff_exists] at hφ
              refine ⟨hφ, ?_⟩
              intro m hm
              cases hc : c m ↑(φ r) with
              | none => rfl
              | some x =>
                have := Nat.find_le (h := (φ r).property) (n := m) (by
                  simp only [hc, Option.isSome_some])
                simp only [Nat.lt_find_iff, not_exists] at hm
                grind
            · rintro ⟨n, hn₁, hn₂, hn₃⟩
              suffices Nat.find (φ r).property = n by grind
              rw [Nat.find_eq_iff]
              simp only [Option.isSome_iff_exists, Option.isNone_iff_eq_none] at hn₂ hn₃
              grind
          simp only [this, measurableSet_setOf]
          rw [←isHom_iff_measurable]
          apply Prop.isHom_exists fun i ↦ ?_
          apply Prop.isHom_and
          · simp only [isHom_const]
          · apply Prop.isHom_and
            · rw [isHom_iff_measurable] at hφ
              fun_prop
            · apply Prop.isHom_forall fun j ↦ ?_
              apply Prop.isHom_forall fun hj ↦ ?_
              fun_prop
        · fun_prop
      · fun_prop
    · fun_prop

end OmegaQuasiBorelSpace.Option
