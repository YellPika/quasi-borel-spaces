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
    simp only [ωSup, Chain.map_coe, Pi.evalOrderHom_coe, Function.comp_apply, Function.eval]
    apply Prop.isHom_dite
    · apply Prop.isHom_exists fun i ↦ ?_
      suffices IsHom fun x ↦ (c i x).isSome by
        simp only [← Option.isSome_iff_exists]
        fun_prop
      fun_prop
    · apply Option.isHom_some
      rw [isHom_def]
      intro φ hφ
      classical
      have : Nonempty A := ⟨(φ 0).property.choose_spec.choose⟩
      let c' : Chain (ℝ → A) := {
        toFun n r := (c (Nat.find (φ r).property + n) (φ r)).getD ‹Nonempty A›.some
        monotone' i j h r := by
          cases hi : c (Nat.find (φ r).property + i) (φ r) with
          | none =>
            have := c.monotone
              (by grind : Nat.find (φ r).property ≤ Nat.find (φ r).property + i)
              (φ r)
            rw [(Nat.find_spec (φ r).property).choose_spec] at this
            simp only [hi, Option.le_none, reduceCtorEq] at this
          | some x =>

          cases hj : c (Nat.find (φ r).property + j) (φ r) with
          | none =>
            have := c.monotone
              (by grind : Nat.find (φ r).property ≤ Nat.find (φ r).property + j)
              (φ r)
            rw [(Nat.find_spec (φ r).property).choose_spec] at this
            simp only [hj, Option.le_none, reduceCtorEq] at this
          | some y =>

          have := c.monotone
            (by grind : Nat.find (φ r).property + i ≤ Nat.find (φ r).property + j)
            (φ r)
          simp only [hi, hj, Option.some_le_some, Option.getD_some, ge_iff_le] at ⊢ this
          exact this
      }
      apply isHom_ωSup c' fun n ↦ ?_
      simp only [Chain, OrderHom.coe_mk, c']
      apply Option.isHom_getD
      · apply isHom_cases (f := fun n x ↦ c n (φ x))
        · apply isHom_comp' (g := fun x ↦ Nat.find (φ x).property) (f := (· + n))
          · fun_prop
          · sorry
        · fun_prop
      · fun_prop
    · fun_prop

end OmegaQuasiBorelSpace.Option
