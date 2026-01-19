module

import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

public section

namespace MeasureTheory

variable {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]

/-- Packs a natural number and a real number into a single real number. -/
noncomputable def pack : A → ℝ :=
  MeasureTheory.embeddingReal _

/-- Unpacks a natural number and a real number from a single real number. -/
noncomputable def unpack [Nonempty A] : ℝ → A :=
  (MeasureTheory.measurableEmbedding_embeddingReal _).invFun

@[simp]
lemma unpack_pack [Nonempty A] (x : A) : unpack (pack x) = x := by
  simp only [unpack, pack]
  apply MeasurableEmbedding.leftInverse_invFun

@[simp, measurability, fun_prop]
lemma measurable_pack : Measurable (pack (A := A)) := by
  unfold pack
  fun_prop

@[simp, measurability, fun_prop]
lemma measurable_unpack [Nonempty A] : Measurable (unpack (A := A)) := by
  unfold unpack
  fun_prop

end MeasureTheory
