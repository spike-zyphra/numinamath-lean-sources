import Mathlib

theorem algebra_14313 {x : ℝ} (hx : (20 * x + 13) ^ ((1 : ℝ) / 3) = 13) (hx' : 20 * x + 13 ≥ 0) :
    x = 546 / 5 := by   
  have h1 : (20 * x + 13) = 13 ^ 3 := by
    have h2 : (20 * x + 13) = ((20 * x + 13) ^ ((1 : ℝ) / 3)) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    rw [hx] at h2
    nlinarith [Real.rpow_nonneg (show (20 * x + 13) ≥ 0 by linarith) (1 / 3 : ℝ)] 
    all_goals nlinarith
  norm_num at h1 
  linarith