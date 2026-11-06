import Mathlib

open Real

theorem algebra_12809 {f : ℚ → ℝ} (hf : ∀ x, x ≠ 0 → x ≠ 1 → f x + f (1 - 1 / x) = log (abs x)) :
    f 2007 = log (2007 / 2006) := by
  have eq1 := hf 2007 (by norm_num) (by norm_num)
  have eq2 := hf (2006 / 2007) (by norm_num) (by norm_num)
  have eq3 := hf (-1 / 2006) (by norm_num) (by norm_num)
  norm_num [log_div, abs_of_pos, abs_of_neg, div_eq_mul_inv] at eq1 eq2 eq3 ⊢
  linarith