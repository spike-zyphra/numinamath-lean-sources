import Mathlib

theorem algebra_235778 (x y : ℝ) :
    ¬(x^3 + x + y + 1 = 0 ∧ y * x^2 + x + y = 0 ∧ y^2 + y - x^2 + 1 = 0) := by 
  intro h
  rcases h with ⟨h₁, h₂, h₃⟩
  nlinarith [sq_nonneg (x^3), sq_nonneg (x^2), sq_nonneg (y + 1), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x + 1), sq_nonneg (x^2 - 1), sq_nonneg (y + x), sq_nonneg (y - x), sq_nonneg (x^3 - 1), sq_nonneg (x^3 + 1)]