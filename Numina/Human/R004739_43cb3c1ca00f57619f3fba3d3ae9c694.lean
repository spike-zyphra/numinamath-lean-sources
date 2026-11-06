import Mathlib

open Real
/-if a = √3 / (sqrt 2 + sqrt 3 + sqrt 5), b =2+ √6 -√10, then the value of a/b is ?-/
theorem algebra_313936 {a b : ℝ}
    (ha : a = sqrt 3 / (sqrt 2 + sqrt 3 + sqrt 5))
    (hb : b = 2 + sqrt 6 - sqrt 10) : a / b = 1 / 4 := by
  rw [ha, hb]
  have h1 : (sqrt 3 / (sqrt 2 + sqrt 3 + sqrt 5)) / (2 + sqrt 6 - sqrt 10) = 1 / 4 := by
    have h2 : (sqrt 2 + sqrt 3 + sqrt 5) * (2 + sqrt 6 - sqrt 10) = 4 * sqrt 3 := by
      have h1 : (sqrt 2 + sqrt 3 + sqrt 5) * (2 + sqrt 6 - sqrt 10) =
        2 * sqrt 2 + sqrt 2 * sqrt 6 - sqrt 2 * sqrt 10 + 2 * sqrt 3 + sqrt 3 * sqrt 6 - sqrt 3 * sqrt 10 + 2 * sqrt 5 + sqrt 5 * sqrt 6 - sqrt 5 * sqrt 10 := by ring
      rw [h1]
      have h2 : sqrt 2 * sqrt 6 = 2 * sqrt 3 := by --compute some basic equations 
        calc
          sqrt 2 * sqrt 6 = sqrt (2 * 6) := by rw [Real.sqrt_mul (by norm_num)]
          _ = sqrt 12 := by norm_num
          _ = sqrt (2^2 * 3) := by norm_num
          _ = 2 * sqrt 3 := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
      have h3 : sqrt 2 * sqrt 10 = 2 * sqrt 5 := by
        calc
          sqrt 2 * sqrt 10 = sqrt (2 * 10) := by rw [Real.sqrt_mul (by norm_num)]
          _ = sqrt 20 := by norm_num
          _ = sqrt (2^2 * 5) := by norm_num
          _ = 2 * sqrt 5 := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
      have h4 : sqrt 3 * sqrt 6 = 3 * sqrt 2 := by
        calc
          sqrt 3 * sqrt 6 = sqrt (3 * 6) := by rw [Real.sqrt_mul (by norm_num)]
          _ = sqrt 18 := by norm_num
          _ = sqrt (3^2 * 2) := by norm_num
          _ = 3 * sqrt 2 := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
      have h5 : sqrt 3 * sqrt 10 = sqrt 30 := by
        calc
          sqrt 3 * sqrt 10 = sqrt (3 * 10) := by rw [Real.sqrt_mul (by norm_num)]
          _ = sqrt 30 := by norm_num
      have h6 : sqrt 5 * sqrt 6 = sqrt 30 := by
        calc
          sqrt 5 * sqrt 6 = sqrt (5 * 6) := by rw [Real.sqrt_mul (by norm_num)]
          _ = sqrt 30 := by norm_num
      have h7 : sqrt 5 * sqrt 10 = 5 * sqrt 2 := by
        calc
          sqrt 5 * sqrt 10 = sqrt (5 * 10) := by rw [Real.sqrt_mul (by norm_num)]
          _ = sqrt 50 := by norm_num
          _ = sqrt (5^2 * 2) := by norm_num
          _ = 5 * sqrt 2 := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
      rw [h2, h3, h4, h5, h6, h7]
      ring_nf
    have h3 : (sqrt 2 + sqrt 3 + sqrt 5) ≠ 0 := by
      have h1 : sqrt 2 > 0 := Real.sqrt_pos.mpr (show (0:ℝ) < (2:ℝ) by norm_num)
      have h2 : sqrt 3 > 0 := Real.sqrt_pos.mpr (show (0:ℝ) < (3:ℝ) by norm_num)
      have h3 : sqrt 5 > 0 := Real.sqrt_pos.mpr (show (0:ℝ) < (5:ℝ) by norm_num)
      linarith [h1, h2, h3]
    have h4 : (2 + sqrt 6 - sqrt 10) ≠ 0 := by
      have h1 : sqrt 6 > 0 := Real.sqrt_pos.mpr (show (0:ℝ) < (6:ℝ) by norm_num)
      have h2 : sqrt 10 > 0 := Real.sqrt_pos.mpr (show (0:ℝ) < (10:ℝ) by norm_num)
      have h3 : 2 + sqrt 6 > sqrt 10 := by
        have h4 : (2 + sqrt 6) ^ 2 > (sqrt 10) ^ 2 := by
          have h5 : (2 + sqrt 6) ^ 2 = 4 + 4 * sqrt 6 + (sqrt 6) ^ 2 := by ring
          have h6 : (sqrt 10) ^ 2 = 10 := Real.sq_sqrt (show 0 ≤ (10:ℝ) by norm_num)
          have h7 : (sqrt 6) ^ 2 = 6 := Real.sq_sqrt (show 0 ≤ (6:ℝ) by norm_num)
          rw [h5, h7]
          have h8 : 4 * sqrt 6 > 0 := by linarith [h1]
          nlinarith [h8]
        have h4 : 2 + sqrt 6 > 0 := by linarith [h1]
        have h5 : sqrt 10 ≥ 0 := Real.sqrt_nonneg 10
        nlinarith [h4, h5, Real.sq_sqrt (show (0:ℝ) ≤ (10:ℝ) by norm_num), sq_nonneg (2 + sqrt 6), sq_nonneg (sqrt 10)]
      linarith [h3]
    field_simp [h3, h4]
    simp [h2]
    ring
  exact h1