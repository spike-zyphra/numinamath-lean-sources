import Mathlib

theorem algebra_96288 (y : ℝ) (h : (10 : ℝ)^(2 * y) = 25) : (10 : ℝ)^(-y) = 1 / 5 := by
  have h1 : (10 : ℝ) ^ (2 * y) = ((10 : ℝ) ^ y) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    ring_nf
    all_goals linarith
  rw [h1] at h
  have h2 : (10 : ℝ) ^ y > 0 := by
    positivity
  have h3 : (10 : ℝ) ^ y = 5 := by
    nlinarith [h, h2]
  have h4 : (10 : ℝ) ^ (-y) = 1 / ((10 : ℝ) ^ y) := by
    simp [← Real.rpow_neg]
  rw [h4]
  rw [h3]