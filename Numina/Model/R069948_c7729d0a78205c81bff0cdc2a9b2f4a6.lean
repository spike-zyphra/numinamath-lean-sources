import Mathlib

theorem algebra_269810 (x : ℝ) (hx : 4*x^4-12*x^3-7*x^2+22*x+14=0) :
    x=1/2+Real.sqrt 2 ∨ x=1/2-Real.sqrt 2 ∨ x=1+Real.sqrt 3 ∨ x=1-Real.sqrt 3 := by
  have h1 : (x - (1/2 + Real.sqrt 2)) * (x - (1/2 - Real.sqrt 2)) * (x - (1 + Real.sqrt 3)) * (x - (1 - Real.sqrt 3)) = 0 := by
    nlinarith [sq_nonneg (x * 2 - 1), sq_nonneg (x - 1), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (2: ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (3: ℝ) ≥ 0 by norm_num)]
  cases' (mul_eq_zero.1 h1) with h2 h3
  cases' (mul_eq_zero.1 h2) with h4 h5
  cases' (mul_eq_zero.1 h4) with h6 h7
  · -- Case where $x - (1/2 + \sqrt{2}) = 0$
    left
    linarith
  · -- Case where $x - (1/2 - \sqrt{2}) = 0$
    right
    left
    linarith
  · -- Case where $x - (1 + \sqrt{3}) = 0$
    right
    right
    left
    linarith
  · -- Case where $x - (1 - \sqrt{3}) = 0$
    right
    right
    right
    linarith