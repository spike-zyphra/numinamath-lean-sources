import Mathlib

theorem algebra_13045 (x : ℝ) (hx0 : x > 0) (hx : x^3 - 3 * x^2 - x - Real.sqrt 2 = 0) :
    x = 2 + Real.sqrt 2 := by
  have h1 : x^3 - 3 * x^2 - x - Real.sqrt 2 = (x - (2 + Real.sqrt 2)) * (x^2 + ((-1 + Real.sqrt 2)) * x + (-1 + Real.sqrt 2)) := by 
    ring_nf
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  rw [h1] at hx
  cases' (mul_eq_zero.1 hx) with h2 h3
  · -- Case where $x - (2 + \sqrt{2}) = 0$
    linarith 
  · -- Case where the quadratic equals zero 
    nlinarith [sq_nonneg (x + (-1 + Real.sqrt 2) / 2), sq_nonneg (x + (1 - Real.sqrt 2)), sq_nonneg (x - (2 + Real.sqrt 2)), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (x - 2), sq_nonneg (x * (x - (2 + Real.sqrt 2))), Real.sqrt_nonneg 2]