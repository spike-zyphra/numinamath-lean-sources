import Mathlib

theorem inequalities_241333 (x y : ℝ) (h₀ : 0 ≤ y) (h₁ : y * (y + 1) ≤ (x + 1)^2) :
    y * (y - 1) ≤ x^2 := by 
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - y + 1), sq_nonneg (x - y - 1), sq_nonneg (y - 1), sq_nonneg (x), sq_nonneg (y)]