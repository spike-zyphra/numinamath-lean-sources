import Mathlib

theorem algebra_70966 {x y : ℝ} (h₀ : 16*x^3+4*x=16*y+5) (h₁ : 16*y^3+4*y=16*x+5) :
    x=y := by
  have eq2 : (x - y) * (16 * (x^2 + x * y + y^2) + 20) = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x^2 - y^2), sq_nonneg (x * y - y * x), sq_nonneg (x * y), sq_nonneg ((x - y) ^ 2)]
  cases' (mul_eq_zero.mp eq2) with h2 h3
  · -- Case x - y = 0
    linarith
  · -- Case 16 * (x^2 + x * y + y^2) + 20 = 0
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x^2 - y^2), sq_nonneg (x * y - y * x), sq_nonneg (x * y), sq_nonneg ((x - y) ^ 2), sq_pos_of_pos (show (1 : ℝ) > 0 by norm_num)]