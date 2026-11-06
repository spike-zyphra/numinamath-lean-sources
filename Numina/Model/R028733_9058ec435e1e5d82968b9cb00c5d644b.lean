import Mathlib
theorem algebra_610841 (P : ℝ → ℝ) (h : ∀ x : ℝ, (20 * x ^ 27 + 2 * x ^ 2 + 1) * P x = 2001 * x ^ 2001) : P 1 = 87:= by
  have eq1 := h 1
  norm_num at eq1
  linarith