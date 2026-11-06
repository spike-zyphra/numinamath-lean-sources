import Mathlib

theorem algebra_20037 : (Real.sqrt 6 + Real.sqrt 24)^2 = 54 := by
  have h1 : Real.sqrt 24 = 2 * Real.sqrt 6 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  rw [h1]
  have h2 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 24, h2]