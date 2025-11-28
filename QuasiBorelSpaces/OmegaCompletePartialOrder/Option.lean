import Mathlib.Order.OmegaCompletePartialOrder

/-
Faithful ωCPO structure on `Option α` (bottom element `none`, supremum of a chain
given by the first defined element and the ω-supremum of the tail).
-/

namespace OmegaCompletePartialOrder

noncomputable section

variable {α : Type*} [OmegaCompletePartialOrder α]

/-- Bottom-order on options: `none` is bottom, `some` is ordered pointwise. -/
instance : PartialOrder (Option α) where
  le x y :=
    match x, y with
    | none, _ => True
    | some _, none => False
    | some a, some b => a ≤ b
  lt x y :=
    match x, y with
    | none, some _ => True
    | some a, some b => a < b
    | _, _ => False
  le_refl
    | none => trivial
    | some _ => le_rfl
  le_trans
    | none, _, _, _ , _ => trivial
    | some _, none, _, h, _ => False.elim h
    | some _, some _, none, _, hyz => False.elim hyz
    | some a, some b, some c, h1, h2 => le_trans h1 h2
  le_antisymm
    | none, none, _, _ => rfl
    | none, some _, _, hyx => False.elim hyx
    | some _, none, hxy, _ => False.elim hxy
    | some a, some b, hxy, hyx => congrArg some (le_antisymm hxy hyx)
  lt_iff_le_not_ge
    | none, none => by simp
    | none, some _ => by simp
    | some _, none => by simp
    | some a, some b => by simp [lt_iff_le_not_ge]

/-- Pick any index where a chain hits `some` -/
noncomputable def firstSomeIndex (c : Chain (Option α)) (h : ∃ n x, c n = some x) : ℕ :=
  Classical.choose h

/-- A witness that the chain hits `some` at `firstSomeIndex` -/
noncomputable def firstSomeValue (c : Chain (Option α)) (h : ∃ n x, c n = some x) : α :=
  Classical.choose (Classical.choose_spec h)

lemma firstSome_spec (c : Chain (Option α)) (h : ∃ n x, c n = some x) :
    c (firstSomeIndex c h) = some (firstSomeValue c h) := by
  classical
  have := Classical.choose_spec (Classical.choose_spec h)
  simpa using this

/-- Chain of underlying values after the first `some`, padding with the first value -/
noncomputable def tailChain (c : Chain (Option α)) (h : ∃ n x, c n = some x) : Chain α :=
{ toFun := fun k =>
    match c (firstSomeIndex c h + k) with
    | some x => x
    | none => firstSomeValue c h
  monotone' := by
    intro i₁ i₂ hi
    dsimp
    cases hc₁ : c (firstSomeIndex c h + i₁) with
    | none =>
        have hfirst : c (firstSomeIndex c h)
            = some (firstSomeValue c h) := firstSome_spec c h
        have hmono :=
          c.monotone (Nat.le_add_right (firstSomeIndex c h) i₁)
        have : some (firstSomeValue c h) ≤ none := by
          simpa [hfirst, hc₁] using hmono
        cases this
    | some x =>
        have hmono :=
          c.monotone (Nat.add_le_add_left hi (firstSomeIndex c h))
        cases hc₂ : c (firstSomeIndex c h + i₂) with
        | none =>
            have : some x ≤ none := by
              simpa [hc₁, hc₂] using hmono
            cases this
        | some y =>
            have : some x ≤ some y := by
              simpa [hc₁, hc₂] using hmono
            exact this }

@[simp]
lemma tailChain_apply (c : Chain (Option α)) (h : ∃ n x, c n = some x) (k : ℕ) :
    tailChain c h k =
      match c (firstSomeIndex c h + k) with
      | some x => x
      | none => firstSomeValue c h :=
  rfl

/-- ω-supremum on `Option α`: either `none` for an all-bottom chain,
    or `some` of the ω-supremum of the tail of defined elements. -/
noncomputable def optionωSup (c : Chain (Option α)) : Option α := by
  classical
  by_cases h : ∃ n x, c n = some x
  · exact some (ωSup (tailChain c h))
  · exact none

/-- ω-supremum on `Option α`: either `none` for an all-bottom chain,
    or `some` of the ω-supremum of the tail of defined elements -/
noncomputable instance : OmegaCompletePartialOrder (Option α) where
  toPartialOrder := inferInstance
  ωSup := optionωSup
  le_ωSup := by
    intro c i
    classical
    by_cases hc : ∃ n x, c n = some x
    · cases hci : c i with
      | none =>
          have : none ≤ some (ωSup (tailChain c hc)) := by trivial
          simpa [optionωSup, hc, hci] using this
      | some x =>
          have hx_sup : x ≤ ωSup (tailChain c hc) := by
            apply le_ωSup_of_le i
            have hmono :=
              c.monotone (Nat.le_add_left i (firstSomeIndex c hc))
            cases hci' : c (firstSomeIndex c hc + i) with
            | none =>
                have : some x ≤ none := by
                  simpa [hci, hci'] using hmono
                cases this
            | some y =>
                have hxy : x ≤ y := by
                  simpa [hci, hci'] using hmono
                have htail : tailChain c hc i = y := by
                  simp [hci']
                have : x ≤ tailChain c hc i := by
                  simpa [htail] using hxy
                exact this
          simpa [optionωSup, hc, hci] using hx_sup
    · cases hci : c i with
      | none =>
          have : (none : Option α) ≤ none := by trivial
          simp [optionωSup, hc]
      | some x =>
          have : False := hc ⟨i, x, hci⟩
          cases this
  ωSup_le := by
    intro c x hx
    classical
    by_cases hc : ∃ n x, c n = some x
    · have hc' := hc
      rcases hc with ⟨i₀, y₀, hi₀⟩
      cases hxX : x with
      | none =>
          have hcontr : False := by
            have := hx i₀
            simp [ hi₀, hxX] at this
            exact this
          cases hcontr
      | some v =>
          have hv : ωSup (tailChain c hc') ≤ v :=
            OmegaCompletePartialOrder.ωSup_le (c := tailChain c hc') (x := v) (by
              intro j
              have hcx := hx (firstSomeIndex c hc' + j)
              cases hcj : c (firstSomeIndex c hc' + j) with
              | none =>
                  have hfirst : c (firstSomeIndex c hc')
                      = some (firstSomeValue c hc') := firstSome_spec c hc'
                  have hfirst_le : some (firstSomeValue c hc') ≤ some v := by
                    simpa [hfirst, hxX] using hx (firstSomeIndex c hc')
                  have hval : firstSomeValue c hc' ≤ v := by
                    simpa using hfirst_le
                  simpa [tailChain_apply, hcj] using hval
              | some y =>
                  have : some y ≤ some v := by
                    simpa [hcj, hxX] using hcx
                  have : y ≤ v := by
                    simpa using this
                  simpa [tailChain_apply, hcj] using this)
          simp [optionωSup, hc']
          exact hv
    · have : none ≤ x := by
        cases x <;> trivial
      simpa [optionωSup, hc] using this

end

end OmegaCompletePartialOrder
