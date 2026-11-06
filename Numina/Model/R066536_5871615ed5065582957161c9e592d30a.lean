import Mathlib

theorem algebra_111534 {f : ℝ → ℝ} (h : ∀ x y, f x - 2 * x = f y - 2 * y) :
    ∃ a, ∀ x, f x = 2 * x + a := by 
  use f 0
  intro x
  have eq1 := h x 0
  simp at eq1
  linarith