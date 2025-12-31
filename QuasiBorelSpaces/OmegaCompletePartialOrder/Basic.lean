import Mathlib.Order.OmegaCompletePartialOrder
import QuasiBorelSpaces.OmegaCompletePartialOrder.Chain.Const

/-!
# Basic properties of ω-complete partial orders

This file is a placeholder for lemmas about `OmegaCompletePartialOrder`.
As the library grows, compatibility helpers specific to this project can
be added here.
-/

namespace OmegaCompletePartialOrder

variable {A B C : Type*}
  [OmegaCompletePartialOrder A]
  [OmegaCompletePartialOrder B]
  [OmegaCompletePartialOrder C]

attribute [fun_prop]
  ωScottContinuous
  ωScottContinuous.id
  ωScottContinuous.comp
  ωScottContinuous.const

@[simp, fun_prop]
lemma ωScottContinuous_const (x : B) : ωScottContinuous (fun _ : A ↦ x) := ωScottContinuous.const

@[fun_prop]
lemma ωScottContinuous_mk
    {f : A → B} {g : A → C} (hf : ωScottContinuous f) (hg : ωScottContinuous g)
    : ωScottContinuous (fun x ↦ (f x, g x)) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨?_, fun c ↦ ?_⟩
  · simp only [monotone_prodMk_iff, hf.monotone, hg.monotone, and_self]
  · ext : 1
    · simp only [Prod.ωSup_fst]
      rw [hf.map_ωSup]
      rfl
    · simp only [Prod.ωSup_snd]
      rw [hg.map_ωSup]
      rfl

@[fun_prop]
lemma ωScottContinuous_fst
    {f : A → B × C} (hf : ωScottContinuous f)
    : ωScottContinuous (fun x ↦ (f x).1) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨?_, fun c ↦ ?_⟩
  · apply Monotone.comp ?_ hf.monotone
    apply monotone_fst
  · rw [hf.map_ωSup]
    rfl

@[fun_prop]
lemma ωScottContinuous_snd
    {f : A → B × C} (hf : ωScottContinuous f)
    : ωScottContinuous (fun x ↦ (f x).2) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨?_, fun c ↦ ?_⟩
  · apply Monotone.comp ?_ hf.monotone
    apply monotone_snd
  · rw [hf.map_ωSup]
    rfl

@[simp]
lemma ωSup_const (x : A) : ωSup (Chain.const x) = x := by
  apply antisymm (r := (· ≤ ·))
  · simp only [ωSup_le_iff, Chain.const_apply, le_refl, implies_true]
  · apply le_ωSup_of_le 0
    simp only [Chain.const_apply, le_refl]

end OmegaCompletePartialOrder
