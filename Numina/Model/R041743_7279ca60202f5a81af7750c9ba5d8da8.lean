import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12705 (f : ℝ → ℝ) (hf : f = λ x => 4 * cos x + cos (2 * x)) :
    range f = {y | -3 ≤ y ∧ y ≤ 5} := by
  ext y
  simp [hf]
  constructor
  · -- Assume y ∈ range f
    rintro ⟨x, hx⟩
    have h1 : cos (2 * x) = 2 * (cos x) ^ 2 - 1 := by
      rw [cos_two_mul]
    rw [h1] at hx
    have h2 : -1 ≤ cos x := by linarith [neg_one_le_cos x, cos_le_one x]
    have h3 : cos x ≤ 1 := by linarith [neg_one_le_cos x, cos_le_one x]
    constructor
    · -- Show -3 ≤ y
      nlinarith [sq_nonneg (cos x + 1), sq_nonneg (cos x - 1)]
    · -- Show y ≤ 5
      nlinarith [sq_nonneg (cos x + 1), sq_nonneg (cos x - 1)]
  · -- Show that any value in [ -3, 5 ] is attained
    rintro ⟨hy1, hy2⟩
    have h6 : ∃ t, -1 ≤ t ∧ t ≤ 1 ∧ 2 * t ^ 2 + 4 * t - 1 = y := by
      have h7 : -3 ≤ y := by linarith
      have h8 : y ≤ 5 := by linarith
      use (-1 + Real.sqrt (6 + 2 * y) / 2)
      constructor
      · -- Show -1 ≤ (-1 + Real.sqrt (6 + 2 * y) / 2)
        have h9 : Real.sqrt (6 + 2 * y) ≥ 0 := Real.sqrt_nonneg (6 + 2 * y)
        nlinarith [Real.sq_sqrt (show 6 + 2 * y ≥ 0 by linarith)]
      constructor
      · -- Show (-1 + Real.sqrt (6 + 2 * y) / 2) ≤ 1
        have h10 : Real.sqrt (6 + 2 * y) ≥ 0 := Real.sqrt_nonneg (6 + 2 * y)
        nlinarith [Real.sq_sqrt (show 6 + 2 * y ≥ 0 by linarith)]
      · -- Show 2 * (-1 + Real.sqrt (6 + 2 * y) / 2) ^ 2 + 4 * (-1 + Real.sqrt (6 + 2 * y) / 2) - 1 = y
        nlinarith [Real.sqrt_nonneg (6 + 2 * y), Real.sq_sqrt (show 6 + 2 * y ≥ 0 by linarith)]
    rcases h6 with ⟨t, ht1, ht2, heq⟩
    use Real.arccos t
    have h11 : cos (Real.arccos t) = t := by
      apply Real.cos_arccos
      all_goals
        try linarith
        try linarith
    have h12 : cos (2 * (Real.arccos t)) = 2 * (cos (Real.arccos t)) ^ 2 - 1 := by
      rw [cos_two_mul]
    rw [h12, h11]
    linarith