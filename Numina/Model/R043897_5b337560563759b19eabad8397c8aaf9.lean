import Mathlib

open Real Set

theorem inequalities_319749 (a : ℝ) :
    {x | x^2 < abs (x - 1) + a} ⊆ {x | -3 < x ∧ x < 3} ↔ a ≤ 5 := by
  constructor
  · -- Assume {x | x^2 < abs (x - 1) + a} ⊆ {x | -3 < x ∧ x < 3}
    intro h
    by_contra ha
    push_neg at ha
    have h1 : (-3 : ℝ) ∈ {x | x^2 < abs (x - 1) + a} := by
      norm_num [abs]
      all_goals nlinarith
    have h2 : (-3 : ℝ) ∈ {x | -3 < x ∧ x < 3} := by
      apply h
      exact h1
    norm_num at h2
  · -- Assume a ≤ 5
    intro ha x hx
    have h1 : x ^ 2 < abs (x - 1) + a := by
      simpa using hx
    by_cases h2 : x ≥ 1
    · -- Case where x ≥ 1, so |x - 1| = x - 1
      rw [abs_of_nonneg (by linarith)] at h1
      constructor
      · -- Show -3 < x
        nlinarith [sq_nonneg (x - 3), sq_nonneg (x + 3), sq_nonneg (x - 1)]
      · -- Show x < 3
        nlinarith [sq_nonneg (x - 3), sq_nonneg (x + 3), sq_nonneg (x - 1)]
    · -- Case where x < 1, so |x - 1| = 1 - x
      rw [abs_of_neg (by linarith)] at h1
      constructor
      · -- Show -3 < x
        nlinarith [sq_nonneg (x + 3), sq_nonneg (x - 3), sq_nonneg (x - 1)]
      · -- Show x < 3
        nlinarith [sq_nonneg (x + 3), sq_nonneg (x - 3), sq_nonneg (x - 1)]