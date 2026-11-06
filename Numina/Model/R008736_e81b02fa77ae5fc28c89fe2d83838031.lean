import Mathlib

theorem algebra_21448 {a b : ℝ} (ha : a ≤ b) (h : ∀ x, -(x + 1)^2 + 1 = -(x - a)^2 + 5) :
    b - a = 4 := by 
  have h1 := h 0
  have h2 := h 1
  have h3 := h 2
  nlinarith [sq_nonneg (a - 2), sq_nonneg (a - 1), sq_nonneg (a - 3)]