import Mathlib

theorem algebra_1294 (x : ℝ) (hx : (2 : ℝ)^x = 7) : (2 : ℝ)^(2 * x) = 49 := by
  have h1 : (2 : ℝ) ^ (2 * x) = ((2 : ℝ) ^ x) ^ 2 := by 
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    ring_nf
    all_goals norm_num
  rw [h1, hx]
  norm_num