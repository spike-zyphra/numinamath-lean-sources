import Mathlib

open Real

theorem algebra_122248 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z + y + z = 12) :
    logb 4 x + logb 2 y + logb 2 z ≤ 3 := by
  have h1 : logb 4 x = (logb 2 x) / 2 := by
    have h2 : logb 4 x = logb 2 x / logb 2 (4 : ℝ) := by 
      field_simp [logb]
    have h3 : logb 2 (4 : ℝ) = 2 := by
      rw [logb_eq_iff_rpow_eq] <;> norm_num
    rw [h2, h3]
  have h7 : logb 4 x + logb 2 y + logb 2 z = (1 / 2) * logb 2 (x * y^2 * z^2) := by
    rw [h1]
    have h8 : (logb 2 x) / 2 + logb 2 y + logb 2 z = (1 / 2) * (logb 2 x + 2 * (logb 2 y + logb 2 z)) := by ring
    rw [h8]
    have h9 : logb 2 x + 2 * (logb 2 y + logb 2 z) = logb 2 (x * y^2 * z^2) := by
      have h10 : logb 2 x + 2 * (logb 2 y + logb 2 z) = logb 2 x + 2 * logb 2 y + 2 * logb 2 z := by ring
      rw [h10]
      have h11 : logb 2 x + 2 * logb 2 y + 2 * logb 2 z = logb 2 (x * y ^ 2 * z ^ 2) := by
        have h12 : logb 2 (x * y ^ 2 * z ^ 2) = logb 2 x + logb 2 (y^2) + logb 2 (z^2) := by
          rw [logb_mul (by positivity) (by positivity), logb_mul (by positivity) (by positivity)]
        have h13 : logb 2 (y ^ 2) = 2 * logb 2 y := by
          simp [logb_pow]
        have h14 : logb 2 (z ^ 2) = 2 * logb 2 z := by
          simp [logb_pow]
        rw [h12, h13, h14]
        all_goals ring
      linarith
    linarith 
  have h11 : x * y ^ 2 * z ^ 2 ≤ 64 := by
    nlinarith [sq_nonneg (x * y - x / 4), sq_nonneg (x * z - x / 4), sq_nonneg (y * z - 4), sq_nonneg (y - 4), sq_nonneg (z - 4), sq_nonneg (x - (1 / 4)), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, sq_nonneg ((y * z) - 4), sq_nonneg (x * y * z - 4)]
  have h12 : logb 2 (x * y^2 * z^2) ≤ 6 := by 
    have h13 : x * y^2 * z^2 ≤ (64 : ℝ) := h11 
    have h14 : logb 2 (x * y^2 * z^2) ≤ logb 2 (64 : ℝ) := by
      apply Real.logb_le_logb_of_le 
      all_goals
        nlinarith [show 0 < x * y ^ 2 * z ^ 2 by positivity, show 0 < (64 : ℝ) by norm_num]
    have h15 : logb 2 (64 : ℝ) = 6 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    linarith 
  have h13 : (1 / 2) * logb 2 (x * y^2 * z^2) ≤ 3 := by 
    linarith [h12]
  linarith [h7, h13]