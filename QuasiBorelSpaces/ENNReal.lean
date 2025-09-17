import QuasiBorelSpaces.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

namespace QuasiBorelSpace.ENNReal

variable {A : Type*} [QuasiBorelSpace A]

@[fun_prop]
lemma isHom_add
    {f : A → ENNReal} (hf : IsHom f)
    {g : A → ENNReal} (hg : IsHom g)
    : IsHom (fun x ↦ f x + g x) := by
  intro φ hφ
  specialize hg hφ
  specialize hf hφ
  simp only [IsVar_def] at ⊢ hg hf
  exact Measurable.add hf hg

@[fun_prop]
lemma isHom_mul
    {f : A → ENNReal} (hf : IsHom f)
    {g : A → ENNReal} (hg : IsHom g)
    : IsHom (fun x ↦ f x * g x) := by
  intro φ hφ
  specialize hg hφ
  specialize hf hφ
  simp only [IsVar_def] at ⊢ hg hf
  exact Measurable.mul hf hg

end QuasiBorelSpace.ENNReal
