import Mathlib

theorem algebra_95916
  {f : ℝ → ℝ}
  (h : ∀ x > 0, f x + 2 * f (2002 / x) = 3 * x) :
  f 2 = 2000 := by
    have eq1 := h 2 (by norm_num)
    have eq2 := h 1001 (by norm_num)
    norm_num at eq1 eq2 
    linarith