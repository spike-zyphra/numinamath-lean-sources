import Mathlib

theorem algebra_10244 (x1 x2 : ℝ) (hx1 : x1^2-5*x1+5=0) (hx2 : x2^2-5*x2+5=0)
    (hx12 : x1≠x2) :
    |x1-x2| = Real.sqrt 5 := by

  have h1 : x1 + x2 = 5 := by
    have h2 : (x1 - x2) * (x1 + x2 - 5) = 0 := by
      nlinarith

    cases' (mul_eq_zero.1 h2) with h3 h4 
    · -- x1 - x2 = 0
      exfalso
      apply hx12
      linarith
    · -- x1 + x2 - 5 = 0
      linarith
  have h2 : (x1 - x2) ^ 2 = 5 := by
    have h3 : x1 + x2 = 5 := h1
    nlinarith [sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by 
      intro h
      apply hx12
      linarith
    ), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2 - 5)]
  have h3 : |x1 - x2| = Real.sqrt ((x1 - x2) ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
  rw [h3]
  rw [show (x1 - x2) ^ 2 = (5 : ℝ) by linarith [h2]]