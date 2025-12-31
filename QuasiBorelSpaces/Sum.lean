import QuasiBorelSpaces.Bool
import QuasiBorelSpaces.Hom
import QuasiBorelSpaces.Lift
import QuasiBorelSpaces.OmegaCompletePartialOrder.Sum
import QuasiBorelSpaces.OmegaQuasiBorelSpace
import QuasiBorelSpaces.Prop
import QuasiBorelSpaces.Sigma

/-!
# Binary Coproducts of Quasi-Borel Spaces

This file defines binary coproducts of quasi-borel spaces by giving a
`QuasiBorelSpace` instance for the `· ⊕ ·` type.

See [HeunenKSY17], Proposition 17.
-/

namespace QuasiBorelSpace.Sum

universe u v

variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]
  {C : Type*} [QuasiBorelSpace C]
  {D : Type*} [QuasiBorelSpace D]
  {E : Type*} [QuasiBorelSpace E]

/--
We derive the `QuasiBorelSpace` instance for `A ⊕ B` via `Sigma (Encoding A B)`.
-/
def Encoding (A : Type u) (B : Type v) : Bool → Type (max u v)
  | true => ULift A
  | false => ULift B

namespace Encoding

/-- The encoded version of `Sum.inl`. -/
def inl (x : A) : Sigma (Encoding A B) := ⟨true, ⟨x⟩⟩

/-- The encoded version of `Sum.inr`. -/
def inr (x : B) : Sigma (Encoding A B) := ⟨false, ⟨x⟩⟩

/-- The encoded version of `Sum.elim`. -/
def elim (f : A → C) (g : B → C) : Sigma (Encoding A B) → C
  | ⟨true, x⟩ => f x.down
  | ⟨false, x⟩ => g x.down

instance {b : Bool} : QuasiBorelSpace (Encoding A B b) := by
  cases b <;>
  · dsimp only [Encoding]
    infer_instance

@[fun_prop]
lemma isHom_inl : IsHom (inl (A := A) (B := B)) := by
  unfold inl
  fun_prop

@[fun_prop]
lemma isHom_inr : IsHom (inr (A := A) (B := B)) := by
  unfold inr
  fun_prop

@[fun_prop]
lemma isHom_elim {f : A → C} (hf : IsHom f) {g : B → C} (hg : IsHom g) : IsHom (elim f g) := by
  apply Sigma.isHom_elim fun b ↦ ?_
  cases b <;>
  · simp only [elim]
    fun_prop

end Encoding

/-- Encodes an `A ⊕ B` as a `Sigma (Encoding A B)`. -/
def encode : A ⊕ B → Sigma (Encoding A B) :=
  Sum.elim Encoding.inl Encoding.inr

instance : QuasiBorelSpace (A ⊕ B) := lift encode

@[fun_prop]
lemma isHom_encode : IsHom (encode (A := A) (B := B)) := by
  apply isHom_of_lift

@[simp]
lemma isHom_inl : IsHom (Sum.inl : A → A ⊕ B) := by
  simp only [isHom_to_lift, encode, Sum.elim_inl]
  fun_prop

@[fun_prop]
lemma isHom_inl' {f : A → B} (hf : IsHom f) : IsHom (fun x ↦ Sum.inl (f x) : A → B ⊕ C) :=
  isHom_comp isHom_inl hf

@[simp]
lemma isHom_inr : IsHom (Sum.inr : B → A ⊕ B) := by
  simp only [isHom_to_lift, encode, Sum.elim_inr]
  fun_prop

@[fun_prop]
lemma isHom_inr' {f : A → C} (hf : IsHom f) : IsHom (fun x ↦ Sum.inr (f x) : A → B ⊕ C) :=
  isHom_comp isHom_inr hf

@[local fun_prop]
lemma isHom_elim
    {f : A → C} (hf : IsHom f)
    {g : B → C} (hg : IsHom g)
    : IsHom (Sum.elim f g) := by
  have : Sum.elim f g = fun x ↦ Encoding.elim f g (encode x) := by
    ext x
    cases x <;> rfl
  rw [this]
  fun_prop

@[fun_prop]
lemma isHom_elim'
    {f : A → B → D} (hf : IsHom (fun x : A × B ↦ f x.1 x.2))
    {g : A → C → D} (hg : IsHom (fun x : A × C ↦ g x.1 x.2))
    {h : A → B ⊕ C} (hh : IsHom h)
    : IsHom (fun x ↦ Sum.elim (f x) (g x) (h x)) := by
  have {x}
      : Sum.elim (f x) (g x) (h x)
      = Sum.elim (γ := A →𝒒 D) (fun x ↦ .mk (f · x)) (fun x ↦ .mk (g · x)) (h x) x := by
    cases h x <;> rfl
  simp only [this]
  fun_prop

@[fun_prop]
lemma isHom_map
    {f : A → B → D} (hf : IsHom fun x : A × B ↦ f x.1 x.2)
    {g : A → C → E} (hg : IsHom fun x : A × C ↦ g x.1 x.2)
    {h : A → B ⊕ C} (hh : IsHom h)
    : IsHom (fun x ↦ Sum.map (f x) (g x) (h x)) := by
  change IsHom fun x ↦ Sum.elim (Sum.inl ∘ f x) (Sum.inr ∘ g x) (h x)
  fun_prop

@[fun_prop, simp]
lemma isHom_isLeft : IsHom (Sum.isLeft : A ⊕ B → Bool) := by
  have : (Sum.isLeft : A ⊕ B → Bool) = Sum.elim (fun _ ↦ true) (fun _ ↦ false) := by
    ext x
    cases x <;> rfl
  rw [this]
  fun_prop

end QuasiBorelSpace.Sum

namespace OmegaQuasiBorelSpace.Sum

open QuasiBorelSpace
open OmegaCompletePartialOrder

variable {A B : Type*}

/-- Coproduct of omega quasi-borel spaces is again an omega quasi-borel space. -/
noncomputable instance instOmegaQuasiBorelSpaceSum
    [OmegaQuasiBorelSpace A] [OmegaQuasiBorelSpace B] :
    OmegaQuasiBorelSpace (A ⊕ B) where
  isHom_ωSup' c hc := by
    simp only [ωSup]

    wlog hα : Nonempty A
    · have : ∀n r, ∃x, c n r = .inr x := by
        intro n r
        cases c n r with
        | inl x =>
          have : Nonempty A := ⟨x⟩
          contradiction
        | inr x => simp only [Sum.inr.injEq, exists_eq']
      choose x hx using this

      have hx' {a} : Monotone (fun n ↦ x n a) := by
        intro n₁ n₂ hn
        simp only
        suffices Sum.inr (x n₁ a) ≤ (Sum.inr (x n₂ a) : A ⊕ B) by
          simpa only [ge_iff_le, Sum.inr_le_inr_iff] using this
        simp only [← hx]
        apply c.monotone hn

      have hx'' : Monotone x := by
        intro n₁ n₂ hn r
        simp only
        suffices Sum.inr (x n₁ r) ≤ (Sum.inr (x n₂ r) : A ⊕ B) by
          simpa only [ge_iff_le, Sum.inr_le_inr_iff] using this
        simp only [← hx]
        apply c.monotone hn

      have (a : ℝ) : c.map (Pi.evalOrderHom a) = Chain.Sum.inr ⟨fun n ↦ x n a, hx'⟩ := by
        ext n
        simp only [
          Chain.map_coe, Pi.evalOrderHom_coe,
          Function.comp_apply, Function.eval, hx,
          Chain.Sum.inr_apply, Sum.inr.injEq]
        rfl

      simp only [this, Chain.Sum.distrib_inr, Sum.map_inr]
      apply Sum.isHom_inr'
      change IsHom (ωSup ⟨_, hx''⟩)
      apply isHom_ωSup
      intro n
      change IsHom (x n)

      have hα' : IsEmpty A := by simpa only [not_nonempty_iff] using hα
      have : IsHom (fun r ↦ Sum.elim hα'.elim id (c n r)) := by
        apply Sum.isHom_elim'
        · rw [isHom_def]
          intro φ
          have : Nonempty A := ⟨(φ 0).2⟩
          contradiction
        · fun_prop
        · fun_prop

      simp only [hx, Sum.elim_inr, id_eq] at this
      apply this

    wlog hβ : Nonempty B
    · have : ∀n r, ∃x, c n r = .inl x := by
        intro n r
        cases c n r with
        | inr x =>
          have : Nonempty B := ⟨x⟩
          contradiction
        | inl x => simp only [Sum.inl.injEq, exists_eq']
      choose x hx using this

      have hx' {a} : Monotone (fun n ↦ x n a) := by
        intro n₁ n₂ hn
        simp only
        suffices Sum.inl (x n₁ a) ≤ (Sum.inl (x n₂ a) : A ⊕ B) by
          simpa only [ge_iff_le, Sum.inl_le_inl_iff] using this
        simp only [← hx]
        apply c.monotone hn

      have hx'' : Monotone x := by
        intro n₁ n₂ hn r
        simp only
        suffices Sum.inl (x n₁ r) ≤ (Sum.inl (x n₂ r) : A ⊕ B) by
          simpa only [ge_iff_le, Sum.inl_le_inl_iff] using this
        simp only [← hx]
        apply c.monotone hn

      have (a : ℝ) : c.map (Pi.evalOrderHom a) = Chain.Sum.inl ⟨fun n ↦ x n a, hx'⟩ := by
        ext n
        simp only [Chain.map_coe, Pi.evalOrderHom_coe, Function.comp_apply, Function.eval, hx]
        rfl

      simp only [this, Chain.Sum.distrib_inl, Sum.map_inl]
      apply Sum.isHom_inl'
      change IsHom (ωSup ⟨_, hx''⟩)
      apply isHom_ωSup
      intro n
      change IsHom (x n)

      have hβ' : IsEmpty B := by simpa only [not_nonempty_iff] using hβ
      have : IsHom (fun r ↦ Sum.elim id hβ'.elim (c n r)) := by
        apply Sum.isHom_elim'
        · fun_prop
        · rw [isHom_def]
          intro φ
          have : Nonempty B := ⟨(φ 0).2⟩
          contradiction
        · fun_prop

      simp only [hx, Sum.elim_inl, id_eq] at this
      apply this

    have : Inhabited A := ⟨hα.some⟩
    have : Inhabited B := ⟨hβ.some⟩
    simp only [
      Chain.Sum.distrib_def, Chain.map_coe,
      Pi.evalOrderHom_coe, Function.comp_apply, Function.eval]

    simp only [apply_ite, Sum.map_inl, Sum.map_inr]
    apply Prop.isHom_ite
    · apply isHom_cases (f := fun x _ ↦ x = true)
      · fun_prop
      · fun_prop
    · apply Sum.isHom_inl'
      change IsHom (ωSup ⟨_, ?_⟩)
      · apply isHom_ωSup
        intro n
        apply Sum.isHom_elim'
        · fun_prop
        · fun_prop
        · apply hc
      · intro n₁ n₂ hn x
        have : c n₁ x ≤ c n₂ x := c.monotone hn x
        simp only [
          id_eq, Chain.map_coe, Pi.evalOrderHom_coe, Function.comp_apply,
          Function.eval, ge_iff_le]
        cases hcn₁ : c n₁ x with
        | inl cn₁ =>
          cases hcn₂ : c n₂ x with
          | inl hcn₂ => simpa only [hcn₁, hcn₂, Sum.inl_le_inl_iff] using this
          | inr hcn₂ => simp only [hcn₁, hcn₂, Sum.not_inl_le_inr] at this
        | inr cn₁ =>
          cases hcn₂ : c n₂ x with
          | inl hcn₂ => simp only [hcn₁, hcn₂, Sum.not_inr_le_inl] at this
          | inr hcn₂ => simp only [le_refl]
    · apply Sum.isHom_inr'
      change IsHom (ωSup ⟨_, ?_⟩)
      · apply isHom_ωSup
        intro n
        apply Sum.isHom_elim'
        · fun_prop
        · fun_prop
        · apply isHom_comp'
          · apply Sum.isHom_elim'
            · fun_prop
            · fun_prop
            · fun_prop
          · apply hc
      · intro n₁ n₂ hn x
        have : c n₁ x ≤ c n₂ x := c.monotone hn x
        simp only [
          id_eq, Chain.map_coe, Pi.evalOrderHom_coe, Function.comp_apply,
          Function.eval, ge_iff_le]
        cases hcn₁ : c n₁ x with
        | inl cn₁ =>
          cases hcn₂ : c n₂ x with
          | inl hcn₂ => simp only [OrderHom.coe_mk, Sum.swap_inl, le_refl]
          | inr hcn₂ => simp only [hcn₁, hcn₂, Sum.not_inl_le_inr] at this
        | inr cn₁ =>
          cases hcn₂ : c n₂ x with
          | inl hcn₂ => simp only [hcn₁, hcn₂, Sum.not_inr_le_inl] at this
          | inr hcn₂ =>
            simpa only [OrderHom.coe_mk, Sum.swap_inr, hcn₁, hcn₂, Sum.inr_le_inr_iff] using this

end OmegaQuasiBorelSpace.Sum
