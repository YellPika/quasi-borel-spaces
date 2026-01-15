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

variable {A B C : Type*}

@[fun_prop]
lemma isHom_projl
    [Preorder A] [QuasiBorelSpace A]
    [Preorder B] [QuasiBorelSpace B]
    [QuasiBorelSpace C]
    {f : C → Chain (A ⊕ B)} (hf : IsHom f)
    {g : C → A} (hg : IsHom g)
    : IsHom (fun x ↦ Chain.Sum.projl (hA := ⟨g x⟩) (f x)) := by
  simp only [Chain.isHom_iff, Chain.Sum.projl_coe]
  intro i
  apply Sum.isHom_elim'
  · fun_prop
  · fun_prop
  · apply isHom_comp' (Chain.isHom_apply i) hf

@[fun_prop]
lemma isHom_projr
    [Preorder A] [QuasiBorelSpace A]
    [Preorder B] [QuasiBorelSpace B]
    [QuasiBorelSpace C]
    {f : C → Chain (A ⊕ B)} (hf : IsHom f)
    {g : C → B} (hb : IsHom g)
    : IsHom (fun x ↦ Chain.Sum.projr (hB := ⟨g x⟩) (f x)) := by
  simp only [Chain.isHom_iff, Chain.Sum.projr_coe]
  intro i
  apply Sum.isHom_elim'
  · fun_prop
  · fun_prop
  · apply isHom_comp' (Chain.isHom_apply i) hf

@[fun_prop, simp]
lemma isHom_distrib
    [Preorder A] [QuasiBorelSpace A]
    [Preorder B] [QuasiBorelSpace B]
    : IsHom (Chain.Sum.distrib (A := A) (B := B)) := by
  simp (unfoldPartialApp := true) only [Chain.Sum.distrib]
  fun_prop

/-- Coproduct of omega quasi-borel spaces is again an omega quasi-borel space. -/
noncomputable instance
    [OmegaQuasiBorelSpace A] [OmegaQuasiBorelSpace B] :
    OmegaQuasiBorelSpace (A ⊕ B) where
  isHom_ωSup := by
    simp only [ωSup]
    fun_prop

end OmegaQuasiBorelSpace.Sum
