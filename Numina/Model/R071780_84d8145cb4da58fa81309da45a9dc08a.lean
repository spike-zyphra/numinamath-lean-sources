import Mathlib

theorem inequalities_234876
    (a b : ℝ)
    (h₀ : a < 1)
    (h₁ : b < 1)
    (h₂ : a + b ≥ 1 / 2) :
    (1 - a) * (1 - b) ≤ 9 / 16 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1 / 2), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (a + b - 3 / 2), sq_nonneg (1 - a - b), mul_pos (sub_pos.mpr h₀) (sub_pos.mpr h₁)]