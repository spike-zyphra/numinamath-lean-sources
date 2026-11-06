import Mathlib

theorem algebra_9059 (x : ℝ) :
    |x| - |x - 3| < 2 ↔ x < 5/2 := by
  constructor
  · -- Assume |x| - |x - 3| < 2, we need to show x < 5/2
    intro h
    by_cases h1 : x ≥ 0
    · -- x ≥ 0
      by_cases h2 : x ≥ 3
      · -- x ≥ 3
        rw [abs_of_nonneg (show (x : ℝ) ≥ 0 by linarith), abs_of_nonneg (show (x - 3 : ℝ) ≥ 0 by linarith)] at h
        linarith
      · -- 0 ≤ x < 3
        rw [abs_of_nonneg (show (x : ℝ) ≥ 0 by linarith), abs_of_neg (show (x - 3 : ℝ) < 0 by linarith)] at h
        nlinarith
    · -- x < 0
      rw [abs_of_neg (show (x : ℝ) < 0 by linarith), abs_of_neg (show (x - 3 : ℝ) < 0 by linarith)] at h
      nlinarith
  · -- Assume x < 5/2, we need to show |x| - |x - 3| < 2
    intro h
    by_cases h1 : x ≥ 0
    · -- x ≥ 0
      by_cases h2 : x ≥ 3
      · -- x ≥ 3
        rw [abs_of_nonneg (show (x : ℝ) ≥ 0 by linarith), abs_of_nonneg (show (x - 3 : ℝ) ≥ 0 by linarith)]
        nlinarith
      · -- 0 ≤ x < 3
        rw [abs_of_nonneg (show (x : ℝ) ≥ 0 by linarith), abs_of_neg (show (x - 3 : ℝ) < 0 by linarith)]
        nlinarith
    · -- x < 0
      rw [abs_of_neg (show (x : ℝ) < 0 by linarith), abs_of_neg (show (x - 3 : ℝ) < 0 by linarith)]
      nlinarith