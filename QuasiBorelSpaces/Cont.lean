import QuasiBorelSpaces.OmegaHom

open QuasiBorelSpace
open OmegaCompletePartialOrder

namespace OmegaQuasiBorelSpace

/-- The continuation monad in the category of `OmegaQuasiBorelSpace`s. -/
structure Cont (R A : Type*) [OmegaQuasiBorelSpace R] [OmegaQuasiBorelSpace A] where
  /-- The underlying morphism. -/
  val : (A →ω𝒒 R) →ω𝒒 R

namespace Cont

variable {R A B : Type*} [OmegaQuasiBorelSpace R] [OmegaQuasiBorelSpace A]

@[ext]
lemma ext {x y : Cont R A} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  simp_all only

instance : PartialOrder (Cont R A) :=
  PartialOrder.lift val (by
    rintro ⟨x⟩ ⟨y⟩
    simp only [mk.injEq, imp_self])

instance : OmegaCompletePartialOrder (Cont R A) := by
  refine OmegaCompletePartialOrder.lift ⟨val, ?_⟩ (fun c ↦ ⟨ωSup (c.map ⟨val, ?_⟩)⟩) ?_ ?_
  · rintro ⟨x⟩ ⟨y⟩
    simp only [LE.le, imp_self]
  · rintro ⟨x⟩ ⟨y⟩
    simp only [LE.le, imp_self]
  · intro ⟨x⟩ ⟨y⟩
    simp only [LE.le, OrderHom.coe_mk, imp_self]
  · simp only [OrderHom.coe_mk, implies_true]

instance : QuasiBorelSpace (Cont R A) :=
  QuasiBorelSpace.lift val

@[simp, local fun_prop]
lemma isHom_val : IsHom (val (R := R) (A := A)) := by
  rw [← isHom_to_lift]
  simp only [isHom_id']

@[fun_prop]
lemma isHom_val'
    [QuasiBorelSpace B] {f : B → Cont R A} (hf : IsHom f)
    : IsHom (fun x ↦ (f x).val) := by
  fun_prop

@[simp, local fun_prop]
lemma isHom_mk : IsHom (mk (R := R) (A := A)) := by
  apply isHom_of_lift

@[fun_prop]
lemma isHom_mk'
    [QuasiBorelSpace B] {f : B → (A →ω𝒒 R) →ω𝒒 R} (hf : IsHom f)
    : IsHom (fun x ↦ mk (f x)) := by
  fun_prop

@[simp, local fun_prop]
lemma ωScottContinuous_mk : ωScottContinuous (mk (R := R) (A := A)) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun x y h k ↦ ?_, fun c ↦ ?_⟩
  · apply h
  · rfl

@[fun_prop]
lemma ωScottContinuous_mk'
     [QuasiBorelSpace B] {f : B → (A →ω𝒒 R) →ω𝒒 R} (hf : IsHom f)
     : IsHom (fun x ↦ mk (f x)) := by
  fun_prop

@[simp, local fun_prop]
lemma ωScottContinuous_val : ωScottContinuous (val (R := R) (A := A)) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun x y h k ↦ ?_, fun c ↦ ?_⟩
  · apply h
  · rfl

@[fun_prop]
lemma ωScottContinuous_val'
    [OmegaCompletePartialOrder B] {f : B → Cont R A} (hf : ωScottContinuous f)
    : ωScottContinuous (fun x ↦ (f x).val) := by
  fun_prop

instance : OmegaQuasiBorelSpace (Cont R A) where
  isHom_ωSup' c hc := by
    change IsHom fun x ↦ mk _
    apply isHom_comp'
    · fun_prop
    · let f : (ℝ → Cont R A) →o (ℝ → (A →ω𝒒 R) →ω𝒒 R) := {
        toFun f r := (f r).val
        monotone' i j h r := by apply h
      }
      apply isHom_ωSup (c.map f) fun n ↦ ?_
      simp only [Chain.map_coe, OrderHom.coe_mk, Function.comp_apply, f]
      fun_prop

/-- The `unit` operator (i.e., pure values) for the continuation monad. -/
@[simps]
def unit : A →ω𝒒 Cont R A where
  toFun x := ⟨{ toFun k := k x }⟩

/-- The `bind` operator (i.e., sequential composition) for the continuation monad. -/
@[simps]
def bind [OmegaQuasiBorelSpace B] : (A →ω𝒒 Cont R B) →ω𝒒 (Cont R A →ω𝒒 Cont R B) where
  toFun f := { toFun x := ⟨{ toFun k := x.val { toFun y := (f y).val k } }⟩ }

@[simp]
lemma bind_unit [OmegaQuasiBorelSpace B] (f : A →ω𝒒 Cont R B) (x : A) : bind f (unit x) = f x := rfl

@[simp]
lemma unit_bind : bind (unit (R := R) (A := A)) = .id := rfl

@[simp]
lemma bind_bind {C : Type*}
    [OmegaQuasiBorelSpace B] [OmegaQuasiBorelSpace C]
    (f : B →ω𝒒 Cont R C) (g : A →ω𝒒 Cont R B)
    : (bind f).comp (bind g) = bind ((bind f).comp g) :=
  rfl

end Cont

end OmegaQuasiBorelSpace
