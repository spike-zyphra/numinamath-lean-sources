import Mathlib

theorem algebra_316321 (x y : ℝ) (h : 17 * (x ^ 2 + y ^ 2) - 30 * x * y - 16 = 0) :
    Real.sqrt (16 * x ^ 2 + 4 * y ^ 2 - 16 * x * y - 12 * x + 6 * y + 9) ≤ 7 := by
  have h1 : 16 * x ^ 2 + 4 * y ^ 2 - 16 * x * y - 12 * x + 6 * y + 9 ≤ 49 := by 
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (4 * x - 2 * y - 5), 
      sq_nonneg (x - 1), sq_nonneg (y + 1/2), sq_nonneg (4 * x - 2 * y + 3), 
      sq_nonneg (x - y), sq_nonneg (x * 2 - y * 1), 
      sq_nonneg (x * 19 - y * 13), sq_nonneg (x * 13 - y * 19), 
      sq_nonneg ((17 * (x ^ 2 + y ^ 2) - 30 * x * y - 16) ), 
      h]
  have h2 : Real.sqrt (16 * x ^ 2 + 4 * y ^ 2 - 16 * x * y - 12 * x + 6 * y + 9) ≤ Real.sqrt (49) := by 
    apply Real.sqrt_le_sqrt
    linarith [h1]
  have h3 : Real.sqrt (49 : ℝ) = (7 : ℝ) := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
  rw [h3] at h2 
  linarith [h2]