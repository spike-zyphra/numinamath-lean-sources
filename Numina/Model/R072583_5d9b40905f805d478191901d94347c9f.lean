import Mathlib

theorem algebra_266321 (x : ℝ) : |2 * x - 3| = (6 * x + 17) / 11 ↔
    x = 25 / 8 ∨ x = 4 / 7 := by
  constructor
  · -- Assume |2 * x - 3| = (6 * x + 17) / 11, show x = 25 / 8 ∨ x = 4 / 7
    intro h
    cases' eq_or_eq_neg_of_abs_eq h with h1 h2
    · -- Case where |2x - 3| = 2x - 3
      have h3 : 2 * x - 3 = (6 * x + 17) / 11 := by linarith
      have h4 : x = 25 / 8 := by
        linarith
      left
      exact h4
    · -- Case where |2x - 3| = -(2x - 3)
      have h3 : -(2 * x - 3) = (6 * x + 17) / 11 := by linarith
      have h4 : x = 4 / 7 := by
        linarith
      right
      exact h4
  · -- Assume x = 25 / 8 ∨ x = 4 / 7, show |2 * x - 3| = (6 * x + 17) / 11
    rintro (h | h)
    · -- Case where x = 25/8
      rw [h]
      norm_num [abs_of_nonneg]
    · -- Case where x = 4/7
      rw [h]
      norm_num [abs_of_nonpos]