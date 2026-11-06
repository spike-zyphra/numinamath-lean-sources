import Mathlib
open Real
theorem algebra_102997 {f : ℝ → ℝ} (hf : ∀ x ≠ 0, (27 * f (-x)) / x - x ^ 2 * f (1 / x) = -2 * x ^ 2) :
    f 3 = 2 := by
  have eq1 := hf 3 (by norm_num)
  have eq2 := hf (1/3) (by norm_num)
  have eq3 := hf (-3) (by norm_num)
  have eq4 := hf (-1/3) (by norm_num)
  norm_num at eq1 eq2 eq3 eq4 
  linarith