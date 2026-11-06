import Mathlib

/- Find the constant $t$ such that \[(5x^2 - 6x + 7)(4x^2 +tx + 10) = 20x^4 -54x^3 +114x^2 -102x +70.\] -/
theorem algebra_15783 (t : ℝ) (h : ∀ x, (5 * x ^ 2 - 6 * x + 7) * (4 * x ^ 2 + t * x + 10) = 20 * x ^ 4 - 54 * x ^ 3 + 114 * x ^ 2 - 102 * x + 70) :
    t = -6 := by
  have h₁ := h 1
  have h₂ := h 0
  have h₃ := h 2
  linarith