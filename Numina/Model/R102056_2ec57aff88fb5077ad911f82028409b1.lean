import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_325812 {x : ℝ} (hx : abs (sqrt ((x - 2)^2) - 1) = x) :
    x = 1 / 2 := by
  have h1 : sqrt ((x - 2) ^ 2) = |x - 2| := by
    rw [Real.sqrt_sq_eq_abs]
  rw [h1] at hx
  by_cases h2 : |x - 2| - 1 ≥ 0
  · -- Case where |x - 2| - 1 ≥ 0, so |x - 2| ≥ 1
    have h3 : abs (|x - 2| - 1) = |x - 2| - 1 := by
      rw [abs_of_nonneg h2]
    rw [h3] at hx
    by_cases h4 : x - 2 ≥ 0
    · -- Case where x ≥ 2
      have h5 : |x - 2| = x - 2 := by
        rw [abs_of_nonneg h4]
      rw [h5] at hx
      linarith
    · -- Case where x < 2
      have h6 : |x - 2| = 2 - x := by
        rw [abs_of_neg (show x - 2 < 0 by linarith)]
        all_goals linarith
      rw [h6] at hx
      nlinarith
  · -- Case where |x - 2| - 1 < 0, so |x - 2| < 1
    have h7 : abs (|x - 2| - 1) = 1 - |x - 2| := by
      rw [abs_of_neg (lt_of_not_ge h2)]
      all_goals linarith
    rw [h7] at hx
    by_cases h8 : x - 2 ≥ 0
    · -- Case where x ≥ 2
      have h9 : |x - 2| = x - 2 := by
        rw [abs_of_nonneg h8]
      rw [h9] at hx
      nlinarith
    · -- Case where x < 2
      have h10 : |x - 2| = 2 - x := by
        rw [abs_of_neg (show x - 2 < 0 by linarith)]
        all_goals linarith
      rw [h10] at hx
      nlinarith