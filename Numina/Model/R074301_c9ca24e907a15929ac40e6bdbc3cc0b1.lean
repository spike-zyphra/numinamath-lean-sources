import Mathlib

theorem algebra_7401 {A B : ℝ} (h : ∀ x : ℝ, (2 * A - 7 * B) * x + (3 * A - 8 * B) = 8 * x + 10) :
    A + B = 2 / 5 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  linarith