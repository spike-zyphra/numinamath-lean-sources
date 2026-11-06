import Mathlib
theorem algebra_608623 (x y : ℝ) (hx : x > 0) (hy : y > 0) (h1 : x - y ^ 2 = 3) (h2 : x ^ 2 + y ^ 4 = 13) : x = (3 + √17) / 2:= by

  have h3 : y ^ 2 = x - 3 := by
    nlinarith

  have h4 : y ^ 4 = (y ^ 2) ^ 2 := by ring

  rw [show y ^ 4 = (y ^ 2) ^ 2 by ring] at h2
  rw [show y ^ 2 = x - 3 by linarith [h1, h3]] at h2

  have h5 : (x) ^ 2 + (x - 3) ^ 2 = 13 := by
    nlinarith

  have h6 : 2 * (x) ^ 2 - 6 * (x) - 4 = 0 := by
    nlinarith [h5]

  have h7 : (x) ^ 2 - 3 * (x) - 2 = 0 := by
    nlinarith

  have h8 : (x - (3 + Real.sqrt 17) / 2) * (x - (3 - Real.sqrt 17) / 2) = 0 := by
    nlinarith [h7, Real.sqrt_pos.mpr (show 0 < 17 by norm_num), Real.sq_sqrt (show 0 ≤ (17 : ℝ) by norm_num)]

  cases' (mul_eq_zero.mp h8) with h9 h10

  · -- First case
    linarith

  · -- Second case
    nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), Real.sqrt_pos.mpr (show (17 : ℝ) > 0 by norm_num), sq_nonneg (x - 0), sq_nonneg (y - 0)]