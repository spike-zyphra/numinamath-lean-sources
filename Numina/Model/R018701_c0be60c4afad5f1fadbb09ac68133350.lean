import Mathlib

theorem algebra_298503 {f : ℝ → ℝ} (h : ∀ x, x ≠ 1 → f (1 / (1 - x)) = x * f x + 1) :
    f 5 = 4 / 5 := by

  have eq1 := h 5 (by norm_num)
  norm_num at eq1

  have eq2 := h (-1 / 4) (by norm_num)
  norm_num at eq2

  have eq3 := h (4 / 5) (by norm_num)
  norm_num at eq3

  have eq4 : f 5 = 4 / 5 := by
    linarith [eq1, eq2, eq3]

  exact_mod_cast eq4