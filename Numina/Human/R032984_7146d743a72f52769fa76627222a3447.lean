import Mathlib

theorem algebra_70966 {x y : ℝ} (h₀ : 16*x^3+4*x=16*y+5) (h₁ : 16*y^3+4*y=16*x+5) :
    x=y := by
  have h_sub : (x - y) * (16 * (x^2 + x * y + y^2) + 20) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h_sub) with hxy h2
  · -- Case where x - y = 0, which means x = y
    linarith
  · -- Case where 16 * (x^2 + x * y + y^2) + 20 = 0
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]