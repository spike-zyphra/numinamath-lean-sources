import Mathlib

theorem algebra_10330 {a b : ℕ} (ha : a > b) (h : ∀ x, x^2 - 16 * x + 60 = (x - a) * (x - b)) :
    3 * b - a = 8 := by
  have eq1 := h 0
  norm_num at eq1