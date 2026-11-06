import Mathlib

theorem algebra_4771 (x : ℝ) : (2 : ℝ)^(3*x) = 7 → (8 : ℝ)^(x+1) = 56 := by
  intro h
  have h1 : (8 : ℝ) ^ (x + 1) = (2 ^ (3 : ℝ)) ^ (x + 1 : ℝ) := by
    norm_num
  rw [h1]
  have h2 : ((2 : ℝ) ^ (3 : ℝ)) ^ (x + 1 : ℝ) = (2 : ℝ) ^ (3 * (x + 1) : ℝ) := by
    rw [← Real.rpow_mul]
    ring_nf
    all_goals linarith
  rw [h2]
  have h3 : (2 : ℝ) ^ (3 * (x + 1) : ℝ) = (2 : ℝ) ^ (3 * x : ℝ) * (2 : ℝ) ^ (3 : ℝ) := by
    rw [show 3 * (x + 1 : ℝ) = 3 * x + 3 by ring]
    rw [Real.rpow_add]
    all_goals linarith
  rw [h3]
  rw [h]
  norm_num