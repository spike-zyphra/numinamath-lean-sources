import Mathlib

theorem algebra_21644 : Real.sqrt (((5 / Real.sqrt 80) + (Real.sqrt 845 / 9) + Real.sqrt 45) / Real.sqrt 5) = 13 / 6 := by
  have h1 : Real.sqrt 80 = 4 * Real.sqrt 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h2 : (5 / Real.sqrt 80 : ℝ) = Real.sqrt 5 / 4 := by
    rw [h1]
    have h3 : Real.sqrt 5 > 0 := by positivity
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h3 : Real.sqrt 845 = 13 * Real.sqrt 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h4 : (Real.sqrt 845 / 9 : ℝ) = (13 * Real.sqrt 5) / 9 := by
    rw [h3]
  have h5 : Real.sqrt 45 = 3 * Real.sqrt 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h7 : ((5 / Real.sqrt 80 : ℝ) + (Real.sqrt 845 / 9 : ℝ) + Real.sqrt 45 : ℝ) / Real.sqrt 5 = (169 / 36 : ℝ) := by
    rw [h2, h4, h5]
    have h8 : Real.sqrt 5 > 0 := by positivity
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  rw [h7]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num