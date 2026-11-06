import Mathlib

theorem algebra_20766 {c : ℝ} (h : ∃ a b, ∀ x, x^2 + 25 * x + c = (a + b * x)^2) :
    c = 625 / 4 := by
  obtain ⟨a, b, h⟩ := h
  have h₁ := h 0
  have h₂ := h 1
  have h₃ := h (-1)
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]