import QuasiBorelSpaces.Hom
import QuasiBorelSpaces.Nat
import QuasiBorelSpaces.Pi
import QuasiBorelSpaces.Subtype

namespace QuasiBorelSpace

/--
A `QuasiBorelSpace` `Functor` is a function `F : Type → Type` such that:
-/
class Functor (F : ∀ A [QuasiBorelSpace A], Type*) where
  /-- 1. `F` maps `QuasiBorelSpace`s to `QuasiBorelSpace`s. -/
  [quasiBorelSpace {A} [QuasiBorelSpace A] : QuasiBorelSpace (F A)]
  /-- 2. There is a mapping from morphisms to morphisms. -/
  map {A B} [QuasiBorelSpace A] [QuasiBorelSpace B] : (A →𝒒 B) → (F A →𝒒 F B)
  /-- 3. The mapping preserves the identity morphism. -/
  map_id {A} [QuasiBorelSpace A] : map (A := A) .id = .id
  /-- 4. The mapping distributes over composition. -/
  map_comp
    {A} [QuasiBorelSpace A]
    {B} [QuasiBorelSpace B]
    {C} [QuasiBorelSpace C]
    (f : B →𝒒 C) (g : A →𝒒 B)
    : (map f).comp (map g) = map (f.comp g)

variable
  {A} [QuasiBorelSpace A]
  {B} [QuasiBorelSpace B]
  {C} [QuasiBorelSpace C]

namespace Functor

attribute [instance] Functor.quasiBorelSpace
attribute [simp] Functor.map_id Functor.map_comp

@[simp]
lemma map_comp_coe
    {F} [Functor F]
    {A} [QuasiBorelSpace A]
    {B} [QuasiBorelSpace B]
    {C} [QuasiBorelSpace C]
    (f : B →𝒒 C) (g : A →𝒒 B) (x : F A)
    : map f (map g x) = map (f.comp g) x := by
  have := congr_arg (DFunLike.coe · x) (Functor.map_comp (F := F) f g)
  simpa only [QuasiBorelHom.comp_coe] using this

end Functor

/-- A `Sequence` is a sequence of types `S : ℕ → Type` such that: -/
class Sequence (S : ℕ → Type*) where
  /-- 1. Every `S n` is a `QuasiBorelSpace`. -/
  [quasiBorelSpace {n} : QuasiBorelSpace (S n)]
  /-- 2. There is a projection from each type to its predecessor. -/
  project (n) : S (n + 1) →𝒒 S n

attribute [instance] Sequence.quasiBorelSpace

/-- The composition of a `Functor` with a `Sequence`. -/
structure Comp (F) [Functor F] (S) [Sequence S] (n : ℕ) where
  private mk ::
  private get : F (S n)

namespace Comp

variable {F} [Functor F] {S} [Sequence S] {n}

@[ext]
lemma ext {x y : Comp F S n} (h : x.get = y.get) : x = y := by
  cases x; cases y; simpa only [mk.injEq]

instance : QuasiBorelSpace (Comp F S n) :=
  lift get

@[fun_prop]
lemma isHom_mk : IsHom (mk (F := F) (S := S) (n := n)) := by
  simp only [isHom_to_lift, isHom_id']

@[fun_prop]
lemma isHom_get : IsHom (get (F := F) (S := S) (n := n)) := by
  apply isHom_of_lift _

@[simps project]
instance {F} [Functor F] {S} [Sequence S] : Sequence (Comp F S) where
  project n := .mk fun x ↦ mk (Functor.map (Sequence.project n) x.get)

end Comp

/-- The `Limit` of a `Sequence` `S` consists of: -/
structure Limit (S) [Sequence S] where
  /-- 1. A sequence of elements, one from each `S n`. -/
  toFun (n) : S n
  /-- 2. A proof that every element is the projection of its successor. -/
  property (n) : Sequence.project n (toFun (n + 1)) = toFun n

namespace Limit

variable {S} [Sequence S]

instance : DFunLike (Limit S) ℕ S where
  coe := toFun
  coe_injective' := by
    rintro ⟨f, _⟩ ⟨g, _⟩ h
    simpa only [mk.injEq] using h

/-- A simps projection for function coercion. -/
def Simps.coe (f : Limit S) : ∀ n, S n := f

initialize_simps_projections Limit (toFun → coe)

@[ext]
lemma ext {f g : Limit S} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

/--
Copy of a `QuasiBorelHom` with a new `toFun` equal to the old one.
Useful to fix definitional equalities.
-/
protected def copy (f : Limit S) (f' : ∀ n, S n) (h : f' = ⇑f) : Limit S where
  toFun := f'
  property := h.symm ▸ f.property

@[simp]
lemma coe_mk {f : ∀ n, S n} (hf : ∀ n, Sequence.project n (f (n + 1)) = f n) : ⇑(mk f hf) = f := rfl

@[simp]
lemma eta (f : Limit S) : mk f f.property = f := rfl

@[simp]
lemma toFun_eq_coe (f : Limit S) : toFun f = ⇑f := rfl

@[simp]
lemma project_coe (n) (f : Limit S) : Sequence.project n (f (n + 1)) = f n := f.property n

private def toSubtype {S} [Sequence S] (x : Limit S)
    : { f : ∀ n, S n // ∀ n, Sequence.project n (f (n + 1)) = f n } :=
  ⟨x.toFun, x.property⟩

instance {S} [Sequence S] : QuasiBorelSpace (Limit S) :=
  lift toSubtype

@[fun_prop]
lemma isHom_mk {S} [Sequence S]
    {f : A → ∀ n, S n} (hf₁ : IsHom f) (hf₂ : ∀ x n, Sequence.project n (f x (n + 1)) = f x n)
    : IsHom (fun x ↦ mk (f x) (hf₂ x)) := by
  simp only [isHom_to_lift, toSubtype, Pi.isHom_iff]
  fun_prop

@[fun_prop]
lemma isHom_coe
    {S} [Sequence S] {f : A → Limit S} (hf : IsHom f) {n}
    : IsHom (fun x ↦ f x n) := by
  have : IsHom (toSubtype (S := S)) := isHom_of_lift _
  change IsHom (fun x ↦ (f x).toSubtype.val n)
  apply isHom_comp' (f := Function.eval n ∘ Subtype.val) (g := toSubtype ∘ f)
  · apply isHom_comp' (Pi.isHom_eval n) (Subtype.isHom_val isHom_id)
  · fun_prop

end Limit

private structure Bundle.{u} : Type _ where
  Carrier : Type u
  [quasiBorelSpace : QuasiBorelSpace Carrier]

attribute [local instance] Bundle.quasiBorelSpace

private def Iter₀ (F) [Functor F] : ℕ → Bundle
  | 0 => .mk PUnit
  | n + 1 => .mk (F (Iter₀ F n).Carrier)

/-- The `Sequence` obtained by iterating a `Functor`. -/
structure Iter (F) [Functor F] (n : ℕ) : Type* where
  private mk ::
  private get : (Iter₀ F n).Carrier

variable {F} [Functor F]

namespace Iter

instance {n} : QuasiBorelSpace (Iter F n) :=
  lift get

@[local fun_prop, simp]
lemma isHom_get {n} : IsHom (get (F := F) (n := n)) :=
  isHom_of_lift get

@[local fun_prop, simp]
lemma isHom_mk {n} : IsHom (mk (F := F) (n := n)) := by
  simp only [isHom_to_lift, isHom_id']

/-- Zero element constructor. -/
def zero : Iter F 0 := .mk ()

instance : Subsingleton (Iter F 0) where
  allEq := by
    rintro ⟨a⟩ ⟨b⟩
    simp only [mk.injEq]
    rfl

/-- Successor element constructor. -/
def succ {n} : F (Iter F n) →𝒒 Iter F (n + 1) where
  toFun x := { get := Functor.map (.mk get) x }
  property := by
    apply isHom_comp isHom_mk
    apply QuasiBorelHom.isHom_coe

/-- Successor element destructor. -/
def unsucc {n} : Iter F (n + 1) →𝒒 F (Iter F n) where
  toFun x := Functor.map (.mk mk) x.get

@[simp]
lemma succ_unsucc {n} (x : Iter F (n + 1)) : succ (unsucc x) = x := by
  cases x
  simp only [
    succ, unsucc, QuasiBorelHom.coe_mk, Functor.map_comp_coe, QuasiBorelHom.eq_comp,
    QuasiBorelHom.eq_id, Functor.map_id, QuasiBorelHom.id_coe]

@[simp]
lemma unsucc_succ {n} (x : F (Iter F n)) : unsucc (succ x) = x := by
  simp only [
    unsucc, succ, QuasiBorelHom.coe_mk, Functor.map_comp_coe, QuasiBorelHom.eq_comp,
    QuasiBorelHom.eq_id, Functor.map_id, QuasiBorelHom.id_coe]

lemma succ_injective {n} {x y : F (Iter F n)} (h : succ x = succ y) : x = y := by
  rw [← unsucc_succ x, ← unsucc_succ y, h]

private def project : ∀ n, Iter F (n + 1) →𝒒 Iter F n
  | 0 => .mk fun _ ↦ .zero
  | n + 1 => succ.comp ((Functor.map (project n)).comp unsucc)

instance : Sequence (Iter F) where
  project {n} := project n

@[simp]
lemma project_zero
    : Sequence.project (S := Iter F) (n := 0)
    = .mk fun _ ↦ zero := by
  rfl

@[simp]
lemma project_succ {n}
    : Sequence.project (S := Iter F) (n := n + 1)
    = succ.comp ((Functor.map (Sequence.project (n := n))).comp unsucc) := by
  rfl

/-- Constructs an `Iter`ated sequence of a `Functor` from an unfolding function. -/
@[simp]
def unfold (f : A →𝒒 F A) : ∀ n, A →𝒒 Iter F n
  | 0 => .mk fun _ ↦ zero
  | n + 1 => .mk fun x ↦ succ (Functor.map (unfold f n) (f x))

end Iter

/-- A functor `F` is continuous if it preserves `Limit`s. -/
class Continuous (F) [Functor F] where
  /-- Folds a `Functor` into a `Limit`. -/
  seq {S} [Sequence S] : F (Limit S) →𝒒 Limit (Comp F S)
  /-- Unfolds a `Functor` out of a `Limit`. -/
  unseq {S} [Sequence S] : Limit (Comp F S) →𝒒 F (Limit S)
  /-- `seq` and `unseq` are inverses. -/
  seq_unseq {S} [Sequence S] : seq.comp (unseq (S := S)) = .id
  /-- `seq` and `unseq` are inverses. -/
  unseq_seq {S} [Sequence S] : unseq.comp (seq (S := S)) = .id

namespace Continuous

attribute [simp] seq_unseq unseq_seq

variable [Continuous F] {S} [Sequence S]

@[simp]
lemma seq_unseq_coe (x : Limit (Comp F S)) : seq (unseq x) = x := by
  have := congr_arg (DFunLike.coe · x) seq_unseq
  simpa only [QuasiBorelHom.comp_coe, QuasiBorelHom.id_coe] using this

@[simp]
lemma unseq_seq_coe (x : F (Limit S)) : unseq (seq x) = x := by
  have := congr_arg (DFunLike.coe · x) unseq_seq
  simpa only [QuasiBorelHom.comp_coe, QuasiBorelHom.id_coe] using this

end Continuous

/-- The greatest fixed point of a `Functor`. -/
structure Nu (F) [Functor F] where
  private mk ::
  private get : Limit (Iter F)

namespace Nu

instance {F} [Functor F] : QuasiBorelSpace (Nu F) :=
  lift get

@[local fun_prop, simp]
lemma isHom_get : IsHom (get (F := F)) :=
  isHom_of_lift get

@[local fun_prop, simp]
lemma isHom_mk : IsHom (mk (F := F)) := by
  simp only [isHom_to_lift (A := Nu F), isHom_id']

@[simps]
private def shift : Limit (Iter F) →𝒒 Limit (Comp F (Iter F)) where
  toFun x := {
    toFun n := .mk (Iter.unsucc (x (n + 1)))
    property n := by
      simp only [Comp.project_def, QuasiBorelHom.coe_mk, Comp.mk.injEq]
      apply Iter.succ_injective
      simp only [Iter.succ_unsucc]
      have := congr_arg (DFunLike.coe · (x (n + 1 + 1))) (Iter.project_succ (F := F) (n := n))
      simp only [Limit.project_coe, QuasiBorelHom.comp_coe] at this
      rw [this]
  }

@[simps -fullyApplied]
private def unshift : Limit (Comp F (Iter F)) →𝒒 Limit (Iter F) where
  toFun x := {
    toFun
      | 0 => .zero
      | n + 1 => .succ (x n).get
    property n := by
      cases n with
      | zero => simp only [Nat.reduceAdd, Iter.project_zero, QuasiBorelHom.coe_mk]
      | succ n =>
        simp only [Iter.project_succ, QuasiBorelHom.comp_coe, Iter.unsucc_succ]
        congr 1
        simp only [← x.project_coe n, Comp.project_def, QuasiBorelHom.coe_mk]
  }
  property := by
    apply Limit.isHom_mk
    simp only [Pi.isHom_iff]
    intro n
    cases n with
    | zero => fun_prop
    | succ n => fun_prop

@[simp]
private lemma shift_unshift_coe (x : Limit (Comp F (Iter F))) : shift (unshift x) = x := by
  ext n
  simp only [shift_coe_coe_get, unshift_coe_coe, Iter.unsucc_succ]

@[simp]
private lemma unshift_shift_coe (x : Limit (Iter F)) : unshift (shift x) = x := by
  ext n
  cases n with
  | zero => subsingleton
  | succ n => simp only [unshift_coe_coe, shift_coe_coe_get, Iter.succ_unsucc]

/-- Rolls a `Functor` into a `Nu`. -/
def roll [Continuous F] : F (Nu F) →𝒒 Nu F where
  toFun x := .mk (unshift (Continuous.seq (Functor.map (.mk get) x)))

/-- Unrolls a `Functor` out of a `Nu`. -/
def unroll [Continuous F] : Nu F →𝒒 F (Nu F) where
  toFun x := Functor.map (.mk mk) (Continuous.unseq (shift x.get))

@[simp]
lemma roll_unroll [Continuous F] (x : Nu F) : roll (unroll x) = x := by
  rcases x with ⟨x⟩
  simp only [roll, unroll, QuasiBorelHom.coe_mk, Functor.map_comp_coe, mk.injEq]
  ext n
  cases n with
  | zero => subsingleton
  | succ n =>
    simp only [
      QuasiBorelHom.eq_comp, QuasiBorelHom.eq_id, Functor.map_id,
      QuasiBorelHom.id_coe, Continuous.seq_unseq_coe, unshift_shift_coe]

@[simp]
lemma unroll_roll [Continuous F] (x : F (Nu F)) : unroll (roll x) = x := by
  simp only [
    unroll, roll, QuasiBorelHom.coe_mk, shift_unshift_coe,
    Continuous.unseq_seq_coe, Functor.map_comp_coe, QuasiBorelHom.eq_comp,
    QuasiBorelHom.eq_id, Functor.map_id, QuasiBorelHom.id_coe]

/-- Constructs a `Nu` from an unfolding. -/
def unfold (f : A →𝒒 F A) : A →𝒒 Nu F where
  toFun x := {
    get := {
      toFun n := Iter.unfold f n x
      property n := by
        induction n generalizing x with
        | zero => simp only [Nat.reduceAdd, Iter.project_zero, Iter.unfold, QuasiBorelHom.coe_mk]
        | succ n ih =>
          simp only [
            Iter.project_succ, Iter.unfold, QuasiBorelHom.coe_mk,
            QuasiBorelHom.comp_coe, Iter.unsucc_succ, Functor.map_comp_coe]
          congr 3
          ext y
          simp only [QuasiBorelHom.comp_coe, QuasiBorelHom.coe_mk, ← ih, Iter.unfold]
    }
  }

end Nu

end QuasiBorelSpace
