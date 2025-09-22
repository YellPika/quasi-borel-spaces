import QuasiBorelSpaces.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

namespace QuasiBorelSpace.ENNReal

variable {A : Type*} [QuasiBorelSpace A]

@[fun_prop]
lemma isHom_add
    {f : A → ENNReal} (hf : IsHom f)
    {g : A → ENNReal} (hg : IsHom g)
    : IsHom (fun x ↦ f x + g x) := by
  rw [isHom_def] at ⊢ hf hg
  intro φ hφ
  specialize hg hφ
  specialize hf hφ
  simp only [isHom_ofMeasurableSpace] at ⊢ hg hf
  exact Measurable.add hf hg

@[fun_prop]
lemma isHom_mul
    {f : A → ENNReal} (hf : IsHom f)
    {g : A → ENNReal} (hg : IsHom g)
    : IsHom (fun x ↦ f x * g x) := by
  rw [isHom_def] at ⊢ hf hg
  intro φ hφ
  specialize hg hφ
  specialize hf hφ
  simp only [isHom_ofMeasurableSpace] at ⊢ hg hf
  exact Measurable.mul hf hg

end QuasiBorelSpace.ENNReal
