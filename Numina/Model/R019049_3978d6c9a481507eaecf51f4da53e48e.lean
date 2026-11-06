import Mathlib

theorem algebra_125882 {x y u v : ℝ} (h₀ : x ^ 2 + y ^ 2 = 1) (h₁ : u ^ 2 + v ^ 2 = 1)
    (h₂ : x * u + y * v = 0) : x * y + u * v = 0 := by
  nlinarith [sq_nonneg (x - v), sq_nonneg (y - u), sq_nonneg (x + v), sq_nonneg (y + u)]