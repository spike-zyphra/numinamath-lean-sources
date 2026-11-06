import Mathlib

theorem calculus_14044 (r k : ℝ) (h : ∀ t, 1 + k * t = 3 * (r + 4 * t) - 11) :
    r = 4 ∧ k = 12 := by
  have eq1 := h 0
  have eq2 := h 1
  have hr : r = 4 := by
    linarith
  have hk : k = 12 := by
    rw [hr] at eq2
    linarith
  constructor
  · exact hr
  · exact hk