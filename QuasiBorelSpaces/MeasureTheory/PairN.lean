import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.Tactic.FunProp

namespace MeasureTheory

/-- Packs a natural number and a real number into a single real number. -/
noncomputable def pairN : ℕ × ℝ → ℝ :=
  MeasureTheory.embeddingReal _

/-- Unpacks a natural number and a real number from a single real number. -/
noncomputable def unpairN : ℝ → ℕ × ℝ :=
  (MeasureTheory.measurableEmbedding_embeddingReal _).invFun

@[simp]
lemma unpairN_pairN (x : ℕ × ℝ) : unpairN (pairN x) = x := by
  simp only [unpairN, pairN]
  apply MeasurableEmbedding.leftInverse_invFun

@[simp, measurability, fun_prop]
lemma measurable_pairN : Measurable pairN := by
  unfold pairN
  fun_prop

@[simp, measurability, fun_prop]
lemma measurable_unpairN : Measurable unpairN := by
  unfold unpairN
  fun_prop

end MeasureTheory
