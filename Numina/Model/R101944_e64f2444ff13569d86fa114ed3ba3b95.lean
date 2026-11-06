import Mathlib

theorem algebra_598311 {a b c : ℝ} (h : a * b + a + 1 ≠ 0 ∧ b * c + b + 1 ≠ 0 ∧ c * a + c + 1 ≠ 0) :
    a / (a * b + a + 1) + b / (b * c + b + 1) + c / (c * a + c + 1) +
    ((1 - a * b * c) ^ 2 / ((a * b + a + 1) * (b * c + b + 1) * (c * a + c + 1))) = 1 := by
  have h1 : a * b + a + 1 ≠ 0 := h.1
  have h2 : b * c + b + 1 ≠ 0 := h.2.1
  have h3 : c * a + c + 1 ≠ 0 := h.2.2
  field_simp [(show a * b + a + 1 ≠ 0 by exact h1), (show b * c + b + 1 ≠ 0 by exact h2), (show c * a + c + 1 ≠ 0 by exact h3)]
  ring