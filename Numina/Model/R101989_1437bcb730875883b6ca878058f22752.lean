import Mathlib

theorem algebra_275786 {a b c : ℝ} (ha : a ≠ 0) (h1 : ∀ x, a * (x - 2) ^ 2 + c = (2 * x - 5) * (x - b)) :
    b = 3 / 2 := by 
  have eq1 := h1 0
  have eq2 := h1 1
  have eq3 := h1 2
  simp at eq1 eq2 eq3 
  linarith [eq1, eq2, eq3]