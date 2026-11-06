import Mathlib

theorem algebra_126882 (d : ℝ) (h₀ : d > 0) (h₁ : (d + 1) ^ 2 = 3 * (d - 1)) :
    d = 2 := by 
  nlinarith [sq_nonneg (d - 1 / 2)]