import Mathlib

theorem algebra_4848 (a b c : ℝ) (h : ∀ x, 3 * (x - 3) ^ 2 - 1219 * (x - 3) - 2023 = a * x ^ 2 + b * x + c) : a + b + c = 427 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  linarith