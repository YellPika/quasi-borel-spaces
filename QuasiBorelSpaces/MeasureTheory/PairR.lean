import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.Tactic.FunProp

namespace MeasureTheory

/-- Packs two real numbers into a single real number. -/
noncomputable def pairR : ℝ × ℝ → ℝ :=
  MeasureTheory.embeddingReal _

/-- Unpacks two real numbers from a single real number. -/
noncomputable def unpairR : ℝ → ℝ × ℝ :=
  (MeasureTheory.measurableEmbedding_embeddingReal _).invFun

@[simp]
lemma unpairR_pairR (x : ℝ × ℝ) : unpairR (pairR x) = x := by
  simp only [unpairR, pairR]
  apply MeasurableEmbedding.leftInverse_invFun

@[simp, measurability, fun_prop]
lemma measurable_pairR : Measurable pairR := by
  unfold pairR
  fun_prop

@[simp, measurability, fun_prop]
lemma measurable_unpairR : Measurable unpairR := by
  unfold unpairR
  fun_prop

end MeasureTheory
