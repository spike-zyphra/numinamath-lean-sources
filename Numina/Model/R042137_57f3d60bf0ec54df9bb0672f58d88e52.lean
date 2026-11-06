import Mathlib

theorem algebra_195601 (x : ℝ) (hx : 3*x^3+2*Real.sqrt 3*x^2-21*x+6*Real.sqrt 3=0) :
    (x=Real.sqrt 3 ∨ x=Real.sqrt 3 / 3 ∨ x=-2 * Real.sqrt 3) := by
  have h1 : Real.sqrt 3 > 0 := by
    apply Real.sqrt_pos.mpr
    norm_num
  have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3 : (x - Real.sqrt 3) * (x - Real.sqrt 3 / 3) * (x + 2 * Real.sqrt 3) = 0 := by
    nlinarith [sq_nonneg (x - Real.sqrt 3), sq_nonneg (x - Real.sqrt 3 / 3), sq_nonneg (x + 2 * Real.sqrt 3), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (x ^ 2), sq_nonneg ((x * Real.sqrt 3) ^ 2), Real.sqrt_nonneg 3, sq_nonneg (x - Real.sqrt 3 / 3), sq_nonneg (x + 2 * Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  cases' (mul_eq_zero.mp h3) with h4 h5
  cases' (mul_eq_zero.mp h4) with h6 h7
  · -- Case x - Real.sqrt 3 = 0
    left
    linarith
  · -- Case x - Real.sqrt 3 / 3 = 0
    right
    left
    linarith
  · -- Case x + 2 * Real.sqrt 3 = 0
    right
    right
    nlinarith