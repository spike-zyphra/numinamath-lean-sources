import Mathlib

theorem algebra_74 (a b M N : ℝ) (h₁ : a * 1 ^ 3 + b * 1 + 5 = M) (h₂ : a * (-1) ^ 3 + b * (-1) + 5 = N) : M + N = 10 := by
  linarith