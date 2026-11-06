import Mathlib

theorem algebra_190214 (x y : ℝ) (h : (x - y)^2 = 2 * abs (2 * y - x) + x + 15) :
    x - y + 1 ≤ -2 ∨ x - y + 1 ≥ 6 := by

  by_cases h1 : 2 * y - x ≥ 0
  · -- case 1: 2y - x ≥ 0, i.e., |2y - x| = 2y - x
    have h2 : abs (2 * y - x) = (2 * y - x) := by
      rw [abs_of_nonneg h1]
    rw [h2] at h
    by_cases h3 : x - y ≤ -3
    · -- $x - y \leq -3$
      left
      linarith
    · -- $x - y > -3$
      by_cases h4 : x - y ≥ 5
      · -- $x - y \geq 5$
        right
        linarith
      · -- $x - y < 5$
        nlinarith [sq_nonneg (x - y - 5), sq_nonneg (y - (x - y)), sq_nonneg (x - 2 * y)]
  · -- case 2: 2y - x < 0, i.e., |2y - x| = x - 2y
    have h11 : 2 * y - x < 0 := by linarith
    have h2 : abs (2 * y - x) = (x - 2 * y) := by
      rw [abs_of_neg h11]
      all_goals linarith
    rw [h2] at h
    by_cases h3 : x - y ≤ -3
    · -- $x - y \leq -3$
      left
      linarith
    · -- $x - y > -3$
      by_cases h4 : x - y ≥ 5
      · -- $x - y \geq 5$
        right
        linarith
      · -- $x - y < 5$
        nlinarith [sq_nonneg (x - y - 5), sq_nonneg (y - (x - y)), sq_nonneg (x - 2 * y)]