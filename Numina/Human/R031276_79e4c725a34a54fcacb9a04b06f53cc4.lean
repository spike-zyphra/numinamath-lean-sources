import Mathlib

theorem algebra_5021 {k : ℝ} (h : ∃ x y, y = x^2 + (k + 1)*x + (3*k + 5) ∧
y = x^2 + (2*k + 3)*x + (2*k + 7) ∧ y = x^2 + (3*k - 1)*x + (k + 6)) :
k = 2 / 3 := by 

-- Extract point (x,y) and equations
  obtain ⟨x, y, h₁, h₂, h₃⟩ := h
-- Solve system automatically
  nlinarith