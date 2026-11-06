import Mathlib

theorem algebra_288677 (x y : ℝ) (h : 2 * x ^ 2 + 3 * y ^ 2 = 6 * y) :
    x + y ≤ 1 + Real.sqrt 10 / 2 := by
  have h1 : (Real.sqrt 10 : ℝ) ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have h2 : 2 * x ^ 2 + 3 * (y - 1) ^ 2 = 3 := by
    nlinarith
  have h4 : (x + (y - 1)) ^ 2 ≤ 5 / 2 := by
    nlinarith [sq_nonneg (x - 3 * Real.sqrt 10 / 10), sq_nonneg ((y - 1) - Real.sqrt 10 / 5), 
          sq_nonneg (x + (y - 1) - Real.sqrt 10 / 2), 
          sq_nonneg (x - (y - 1) * 3 / 2), sq_nonneg ((y - 1) - 3 * x / 2), 
          Real.sqrt_pos.mpr (show 0 < (10 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
  have h5 : (x + (y - 1)) ≤ Real.sqrt (5 / 2) := by
    have h6 : (x + (y - 1)) ^ 2 ≤ 5 / 2 := h4
    have h7 : (x + (y - 1)) ≤ Real.sqrt (5 / 2) := by
      apply Real.le_sqrt_of_sq_le
      linarith
    exact h7
  have h6 : Real.sqrt (5 / 2 : ℝ) = Real.sqrt 10 / 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  linarith [h6, h5]