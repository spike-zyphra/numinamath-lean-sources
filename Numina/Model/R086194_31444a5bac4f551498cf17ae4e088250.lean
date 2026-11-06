import Mathlib

theorem algebra_315642 {a b : ℝ} (h : a^3 + b^3 + 3 * a * b = 1) :
    a + b = 1 ∨ a + b = -2 := by
  have h1 : (a + b - 1) * ((a + b)^2 + (a + b) + 1 - 3 * a * b) = 0 := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1), sq_nonneg (a + b + 2)]
  cases' (mul_eq_zero.mp h1) with h2 h3
  · -- Case where $a + b = 1$
    left
    linarith 
  · -- Case where $(a + b)^2 + (a + b) + 1 - 3ab = 0$
    right
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b + 2), sq_nonneg (a * b - 1)]