import Mathlib

theorem algebra_169805 {x : ℝ} (h : abs (1 - x) = 1 + abs x) :
    abs (x - 1) = 1 - x := by
  by_cases h1 : x ≥ 0
  · -- Case x ≥ 0
    by_cases h2 : x ≤ 1
    · -- Case 0 ≤ x ≤ 1
      rw [abs_of_nonneg (by linarith [h1, h2] : (1 - x : ℝ) ≥ 0), abs_of_nonneg (by linarith [h1] : (x : ℝ) ≥ 0)] at h
      have : x = 0 := by linarith [h]
      rw [this]
      norm_num
    · -- Case x > 1
      rw [abs_of_neg (by linarith [show x > 1 by linarith] : (1 - x : ℝ) < 0), abs_of_nonneg (by linarith [h1] : (x : ℝ) ≥ 0)] at h
      linarith
  · -- Case x < 0
    rw [abs_of_pos (by linarith [show x < 0 by linarith] : (1 - x : ℝ) > 0), abs_of_neg (by linarith [show x < 0 by linarith] : (x : ℝ) < 0)] at h
    rw [abs_of_neg (by linarith : (x - 1 : ℝ) < 0)]
    linarith