import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_144354 (f : ℝ → ℝ) (hf : f = λ x => cos x + 1 - π) :
    range f = {y | -π ≤ y ∧ y ≤ 2 - π} := by
  ext y
  simp [hf, mem_range]
  constructor
  · -- Assume y is in the range of f, so there is some x such that y = cos x + 1 - π.
    intro hy
    rcases hy with ⟨x, hx⟩
    have hcos1 : -1 ≤ cos x ∧ cos x ≤ 1 := by
      constructor
      · exact neg_one_le_cos x
      · exact cos_le_one x
    constructor
    · -- Show y ≥ -π
      linarith
    · -- Show y ≤ 2 - π
      linarith
  · -- Assume y ∈ {y | -π ≤ y ∧ y ≤ 2 - π}
    rintro ⟨hy1, hy2⟩
    use Real.arccos (y + Real.pi - 1)
    have hcos : cos (Real.arccos (y + Real.pi - 1)) = y + Real.pi - 1 := by
      apply Real.cos_arccos
      all_goals
        have h1 : -1 ≤ y + Real.pi - 1 := by linarith [Real.pi_gt_three]
        have h2 : y + Real.pi - 1 ≤ 1 := by linarith [Real.pi_gt_three]
        all_goals
          nlinarith [Real.pi_gt_three]
    linarith [hcos]