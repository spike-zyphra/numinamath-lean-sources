import Mathlib

theorem algebra_71176 {x y : ℚ} (h : (x ^ 2 + y ^ 2 - 2) * (x + y) ^ 2 + (x * y + 1) ^ 2 = 0) :
    IsSquare (1 + x * y) := by
  have h1 : (x ^ 2 + x * y + y ^ 2 - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x ^ 2 + x * y + y ^ 2 - 1), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x), sq_nonneg (y), sq_nonneg (x * y), sq_nonneg (x^2 + y^2 - 2), sq_nonneg (x + y), sq_nonneg (x * y + 1)]
  have h2 : x ^ 2 + x * y + y ^ 2 = 1 := by
    have h3 : (x^2 + x * y + y^2 - 1) ^ 2 = 0 := h1
    have h4 : (x^2 + x * y + y^2 - 1) = 0 := by 
      apply pow_eq_zero 
      exact h3 
    linarith 
  have h3 : (1 + x * y) = (x + y) ^ 2 := by
    nlinarith [h2]
  use x + y
  rw [h3]
  all_goals ring