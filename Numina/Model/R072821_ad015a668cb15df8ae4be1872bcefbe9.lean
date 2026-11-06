import Mathlib

open Real

theorem algebra_189543 : (sqrt 6 + 4 * sqrt 3 + 3 * sqrt 2) / ((sqrt 6 + sqrt 3) * (sqrt 3 + sqrt 2)) = sqrt 6 - sqrt 2 := by
  have h1 : (sqrt 6 + sqrt 3) * (sqrt 3 + sqrt 2) ≠ 0 := by
    have h2 : sqrt 6 + sqrt 3 > 0 := by
      have h3 : sqrt 6 > 0 := Real.sqrt_pos.mpr (by norm_num)
      have h4 : sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num)
      linarith
    have h5 : sqrt 3 + sqrt 2 > 0 := by
      have h6 : sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num)
      have h7 : sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
      linarith
    have h8 : (sqrt 6 + sqrt 3) * (sqrt 3 + sqrt 2) > 0 := mul_pos h2 h5
    linarith
  field_simp [h1]
  have h9 : sqrt 18 = 3 * sqrt 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h10 : sqrt 12 = 2 * sqrt 3 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num

  have h13 : sqrt 6 * sqrt 3 = 3 * sqrt 2 := by
    calc
      sqrt 6 * sqrt 3 = sqrt (6 * 3) := by rw [Real.sqrt_mul (by norm_num)]
      _ = sqrt 18 := by norm_num
      _ = 3 * sqrt 2 := by rw [h9]

  have h14 : sqrt 6 * sqrt 2 = 2 * sqrt 3 := by
    calc
      sqrt 6 * sqrt 2 = sqrt (6 * 2) := by rw [Real.sqrt_mul (by norm_num)]
      _ = sqrt 12 := by norm_num
      _ = 2 * sqrt 3 := by rw [h10]

  have h15 : sqrt 3 * sqrt 3 = 3 := by
    calc
      sqrt 3 * sqrt 3 = (sqrt 3) ^ 2 := by ring
      _ = 3 := Real.sq_sqrt (by norm_num)

  have h16 : sqrt 3 * sqrt 2 = sqrt 6 := by
    calc
      sqrt 3 * sqrt 2 = sqrt (3 * 2) := by rw [Real.sqrt_mul (by norm_num)]
      _ = sqrt 6 := by norm_num
  
  nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 3, Real.sqrt_nonneg 2,
          Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
          Real.sqrt_le_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_le_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_le_sqrt (show (0 : ℝ) ≤ 6 by norm_num),
          Real.sqrt_pos.mpr (show (0 : ℝ) < 6 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num),
          h9, h10, h13, h14, h15, h16]