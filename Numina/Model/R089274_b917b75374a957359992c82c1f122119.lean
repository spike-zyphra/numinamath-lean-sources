import Mathlib

theorem algebra_215376 {f : ℝ → ℝ} (h : ∀ x, f (x + 1) + f (x - 1) = 5.2 * f x) (hf0 : f 0 = -98) (hf3 : f 3 = 249.2) :
    f 1 = -10 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  have eq4 := h 3
  norm_num [show f 0 = -98 by linarith, show f 3 = 249.2 by linarith] at eq1 eq2 eq3 eq4
  norm_num [hf0] at eq1 eq2 eq3 eq4
  norm_num [hf3] at eq1 eq2 eq3 eq4
  linarith [eq1, eq2, eq3]