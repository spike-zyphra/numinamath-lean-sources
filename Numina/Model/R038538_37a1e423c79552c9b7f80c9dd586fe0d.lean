import Mathlib

theorem algebra_22166 : 1 / (Real.sqrt 8 + Real.sqrt 50 + Real.sqrt 18) = Real.sqrt 2 / 20 := by
  have h1 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h2 : Real.sqrt 50 = 5 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h3 : Real.sqrt 18 = 3 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h4 : Real.sqrt 8 + Real.sqrt 50 + Real.sqrt 18 = 10 * Real.sqrt 2 := by
    rw [h1, h2, h3]
    ring
  rw [h4]
  have h5 : 0 < (2 : ℝ) := by norm_num
  field_simp [(show (10 * Real.sqrt 2) ≠ 0 by
    have h6 : Real.sqrt 2 > 0 := by
      apply Real.sqrt_pos.mpr
      all_goals norm_num
    have h7 : (10 : ℝ) > 0 := by norm_num
    nlinarith [Real.sqrt_nonneg (2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num ) ]
  ), Real.sqrt_nonneg (2)]
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num