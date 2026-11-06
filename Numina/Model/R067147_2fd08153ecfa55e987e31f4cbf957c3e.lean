import Mathlib

open Real

theorem algebra_202150 {x y z : ℝ}
    (hx : x = (sqrt 7 + sqrt 3) / (sqrt 7 - sqrt 3))
    (hy : y = (sqrt 7 - sqrt 3) / (sqrt 7 + sqrt 3))
    (hz : 192 * z = x ^ 4 + y ^ 4 + (x + y) ^ 4) :
    z = 6 := by
  have h1 : x = (5 + Real.sqrt 21) / 2 := by
    rw [hx]
    have h2 : (sqrt 7 - sqrt 3) ≠ 0 := by
      have h3 : sqrt 7 > sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h4 : sqrt 7 - sqrt 3 > 0 := sub_pos_of_lt h3
      linarith
    field_simp [h2]
    have h5 : sqrt 7 ^ 2 = 7 := by
      rw [Real.sq_sqrt]
      norm_num
    have h6 : sqrt 3 ^ 2 = 3 := by
      rw [Real.sq_sqrt]
      norm_num
    have h7 : sqrt 7 * sqrt 3 = Real.sqrt 21 := by
      calc
        sqrt 7 * sqrt 3 = Real.sqrt (7 * 3) := by rw [Real.sqrt_mul (by norm_num)]
        _ = Real.sqrt 21 := by norm_num
    nlinarith [Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num),
      Real.sq_sqrt (show (7 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num),
      Real.sqrt_nonneg 7, Real.sqrt_nonneg 3, h5, h6, h7]
  have h2 : y = (5 - Real.sqrt 21) / 2 := by
    rw [hy]
    have h8 : (sqrt 7 + sqrt 3) ≠ 0 := by
      have h9 : sqrt 7 > 0 := Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num)
      have h10 : sqrt 3 > 0 := Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)
      nlinarith [Real.sqrt_nonneg 7, Real.sqrt_nonneg 3]
    field_simp [h8]
    have h5 : sqrt 7 ^ 2 = 7 := by
      rw [Real.sq_sqrt]
      norm_num
    have h6 : sqrt 3 ^ 2 = 3 := by
      rw [Real.sq_sqrt]
      norm_num
    have h7 : sqrt 7 * sqrt 3 = Real.sqrt 21 := by
      calc
        sqrt 7 * sqrt 3 = Real.sqrt (7 * 3) := by rw [Real.sqrt_mul (by norm_num)]
        _ = Real.sqrt 21 := by norm_num
    nlinarith [Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num),
      Real.sq_sqrt (show (7 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num),
      Real.sqrt_nonneg 7, Real.sqrt_nonneg 3, h5, h6, h7]
  have h3 : x + y = 5 := by
    rw [h1, h2]
    ring
  have h4 : x * y = 1 := by
    rw [h1, h2]
    nlinarith [Real.sqrt_pos.mpr (show (21 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (21 : ℝ) ≥ 0 by norm_num)]
  have h8 : x ^ 4 + y ^ 4 = 527 := by
    have h9 : x + y = 5 := h3
    have h10 : x * y = 1 := h4
    have h11 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by ring
    rw [h9, h10] at h11
    have h12 : x ^ 2 + y ^ 2 = 23 := by
      nlinarith
    have h13 : x ^ 4 + y ^ 4 = (x ^ 2 + y ^ 2) ^ 2 - 2 * (x * y) ^ 2 := by ring
    rw [h13, h12, h10]
    nlinarith
  have h9 : (x + y) ^ 4 = 625 := by
    rw [h3]
    norm_num
  have eq : x ^ 4 + y ^ 4 + (x + y) ^ 4 = 1152 := by
    nlinarith [h8, h9]
  nlinarith [hz, eq]