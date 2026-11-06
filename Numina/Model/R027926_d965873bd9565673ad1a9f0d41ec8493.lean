import Mathlib

open Real

theorem inequalities_602388 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 + z^2 = 1) :
    x / (1 + x^2) + y / (1 + y^2) + z / (1 + z^2) ≤ 3 * sqrt 3 / 4 := by
  have h1 : sqrt 3 ^ 2 = 3 := by
    rw [Real.sq_sqrt]
    all_goals linarith
  have h2 : sqrt 3 > 0 := by
    apply Real.sqrt_pos.mpr
    all_goals linarith
  have h3 : x / (1 + x^2) ≤ 3 / 8 * x + sqrt 3 / 8 := by
    apply (div_le_iff₀ (by nlinarith)).mpr
    nlinarith [sq_nonneg (x - sqrt 3 / 3), sq_nonneg (x * sqrt 3 - 1 / 3), 
              Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), 
              mul_pos hx (show 0 < (sqrt 3 : ℝ) by positivity)]
  have h4 : y / (1 + y^2) ≤ 3 / 8 * y + sqrt 3 / 8 := by
    apply (div_le_iff₀ (by nlinarith)).mpr
    nlinarith [sq_nonneg (y - sqrt 3 / 3), sq_nonneg (y * sqrt 3 - 1 / 3), 
              Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), 
              mul_pos hy (show 0 < (sqrt 3 : ℝ) by positivity)]
  have h5 : z / (1 + z^2) ≤ 3 / 8 * z + sqrt 3 / 8 := by
    apply (div_le_iff₀ (by nlinarith)).mpr
    nlinarith [sq_nonneg (z - sqrt 3 / 3), sq_nonneg (z * sqrt 3 - 1 / 3), 
              Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), 
              mul_pos hz (show 0 < (sqrt 3 : ℝ) by positivity)]
  have h6 : x / (1 + x^2) + y / (1 + y^2) + z / (1 + z^2) ≤ 3 / 8 * (x + y + z) + 3 * sqrt 3 / 8 := by
    linarith [h3, h4, h5]
  have h7 : x + y + z ≤ sqrt 3 := by
    have h8 : (x + y + z) ^ 2 ≤ 3 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), h]
    have h9 : sqrt 3 ≥ 0 := by positivity
    have h10 : (sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 3, h9, h10, sq_nonneg (x + y + z - sqrt 3)]
  have h8 : 3 / 8 * (x + y + z) + 3 * sqrt 3 / 8 ≤ 3 * sqrt 3 / 4 := by
    nlinarith [h7, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)]
  linarith [h6, h8, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by linarith)]