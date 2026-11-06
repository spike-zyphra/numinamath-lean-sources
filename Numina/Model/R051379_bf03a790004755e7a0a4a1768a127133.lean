import Mathlib

theorem inequalities_78849 (a b c d : ℝ)
    (h₀ : a^2 ≤ 1)
    (h₁ : a^2 + b^2 ≤ 5)
    (h₂ : a^2 + b^2 + c^2 ≤ 14)
    (h₃ : a^2 + b^2 + c^2 + d^2 ≤ 30) :
    a + b + c + d ≤ 10 := by 
  nlinarith [sq_nonneg (a - 1 : ℝ), sq_nonneg (b - 2 : ℝ), sq_nonneg (c - 3 : ℝ), sq_nonneg (d - 4 : ℝ)]