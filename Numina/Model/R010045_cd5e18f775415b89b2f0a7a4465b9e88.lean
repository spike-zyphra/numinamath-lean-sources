import Mathlib

theorem algebra_13280 (a m n : ℝ) (ha : a ≠ 0) (h : ∀ x, -3 * x ^ 2 - 30 * x - 81 = a * (x - m) ^ 2 + n) :
    n = -6 := by
  have h₁ := h 0
  have h₂ := h 1
  have h₃ := h 2
  nlinarith [h₁, h₂, h₃]