import Mathlib

theorem algebra_14562 {f : ℝ → ℝ} (h : ∀ x y, x * f y = y * f x) (h1 : f 15 = 20) : f 3 = 4 := by 
  have eq1 := h 3 15 
  rw [h1] at eq1
  linarith