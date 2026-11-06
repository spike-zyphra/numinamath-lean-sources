import Mathlib

theorem algebra_174868 (n : ℤ) (h : ∀ k, (2 * k + 30) / 2 - k = n) :
    n = 15 := by
  have eq1 := h 0
  norm_num at eq1
  linarith