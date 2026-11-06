import Mathlib

theorem algebra_3604
    (a b c : ℝ)
    (h : ∀ x : ℝ, x * (x - 3) * (x - a) * (x - b) = x ^ 3 - 11 * x ^ 2 + c * x - 36) :
    c = 36 := by

  have eq1 := h 0
  norm_num at eq1
  
  all_goals linarith