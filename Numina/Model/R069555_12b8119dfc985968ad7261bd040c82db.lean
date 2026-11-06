import Mathlib

theorem inequalities_232418 (x : ℝ) :
    abs (x ^ 2 - x) ≤ 2 * x ^ 2 - 3 * x + 1 ↔ x ≤ 1 / 3 ∨ x ≥ 1 := by
  constructor
  · -- Forward implication: if |x² - x| ≤ 2x² - 3x + 1, prove x ≤ 1/3 ∨ x ≥ 1
    intro h
    by_cases h1 : x^2 - x ≥ 0
    · -- Case 1: x^2 - x ≥ 0, so |x^2 - x| = x^2 - x
      rw [abs_of_nonneg h1] at h
      have h2 : x ≤ 0 ∨ x ≥ 1 := by
        by_cases h2 : x ≥ 1
        · -- x ≥ 1, so we can conclude x ≥ 1
          right
          linarith
        · -- x < 1, but since x^2 - x ≥ 0, we have x ≤ 0
          left
          nlinarith
      rcases h2 with h3 | h3
      · -- x ≤ 0: x ≤ 1/3 is trivial
        left
        linarith
      · -- x ≥ 1: directly conclusion
        right
        linarith
    · -- Case 2: x^2 - x < 0, so |x^2 - x| = -(x^2 - x) = x - x^2
      rw [abs_of_neg (lt_of_not_ge h1)] at h
      have h2 : 0 < x := by nlinarith
      have h3 : x < 1 := by nlinarith
      by_cases h4 : x ≤ 1 / 3
      · -- Case 2a: x ≤ 1/3
        left
        linarith
      · -- Case 2b: x > 1/3
        have h5 : 1 / 3 < x := by linarith
        nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (x - 1)]
  · -- Backward implication: if x ≤ 1/3 ∨ x ≥ 1, prove |x² - x| ≤ 2x² - 3x + 1
    rintro (h | h)
    · -- Case 1: x ≤ 1/3
      by_cases h1 : x^2 - x ≥ 0
      · -- Case 1a: x^2 - x ≥ 0, so |x^2 - x| = x^2 - x
        rw [abs_of_nonneg h1]
        nlinarith [sq_nonneg (x - 1)]
      · -- Case 1b: x^2 - x < 0, so |x^2 - x| = -(x^2 - x) = x - x^2
        rw [abs_of_neg (lt_of_not_ge h1)]
        nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (x - 1)]
    · -- Case 2: x ≥ 1
      have h2 : x^2 - x ≥ 0 := by nlinarith
      rw [abs_of_nonneg h2]
      nlinarith [sq_nonneg (x - 1)]