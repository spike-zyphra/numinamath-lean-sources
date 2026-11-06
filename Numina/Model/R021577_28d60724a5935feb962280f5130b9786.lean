import Mathlib

theorem algebra_314024 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : 19 / x + 98 / y = 1) :
    x + y ≥ 117 + 14 * √38 := by
  have h1 : x * y = 19 * y + 98 * x := by
    have h2 : x ≠ 0 := by linarith
    have h3 : y ≠ 0 := by linarith
    field_simp at h
    nlinarith
  have h2 : (x - 19) * (y - 98) = 1862 := by
    nlinarith [h1]
  have h3 : x + y = (x - 19) + (y - 98) + 117 := by
    nlinarith
  have h5 : Real.sqrt 1862 = 7 * Real.sqrt 38 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
    <;> nlinarith [Real.sqrt_nonneg 38]
  have h7 : (x - 19) + (y - 98) ≥ 14 * Real.sqrt 38 := by
    nlinarith [sq_nonneg ((x - 19) - 7 * Real.sqrt 38), sq_nonneg ((y - 98) - 7 * Real.sqrt 38), 
      Real.sqrt_nonneg 38, Real.sq_sqrt (show (0 : ℝ) ≤ (38 : ℝ) by norm_num), 
      h2, mul_pos hx hy, Real.sqrt_nonneg 1862, Real.sq_sqrt (show (0 : ℝ) ≤ (1862 : ℝ) by norm_num), 
      sq_nonneg (Real.sqrt 38 ^ 2), h5]
  linarith [h3, h7, Real.sqrt_nonneg 38]