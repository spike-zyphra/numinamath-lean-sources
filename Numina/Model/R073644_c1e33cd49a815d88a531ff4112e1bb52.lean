import Mathlib

theorem algebra_22043 {z : ℂ} (hz : z = Real.sqrt 5 + 2 * .I) :
    Complex.abs z = 3 := by
  rw [hz]
  simp [Complex.abs, Complex.normSq, Complex.re, Complex.im]
  have h1 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)
  have h2 : Real.sqrt 5 ^ 2 + (2 : ℝ) ^ 2 = 9 := by
    rw [h1]
    norm_num
  have h5 : (5 + (2 : ℝ) * 2) = (9 : ℝ) := by
    norm_num
  have h6 : Real.sqrt ((5 : ℝ) + (2 : ℝ) * 2) = 3 := by
    rw [h5]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  linarith [h6]