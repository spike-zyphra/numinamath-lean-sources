import Mathlib

theorem algebra_152979 (f : ℝ → ℝ) (h : ∀ x y, f x + f (2 * x + y) + 5 * x * y = f (3 * x - y) + 2 * x ^ 2 + 1) :
    f 10 = -49 := by 
  have eq1 := h 10 (5 : ℝ)
  norm_num at eq1 
  linarith