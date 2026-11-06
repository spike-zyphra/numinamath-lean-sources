import Mathlib

theorem algebra_241073 {f : ℝ → ℝ} (hf : ∀ x > 0, 3 * f x + 7 * f (2016 / x) = 2 * x) :
    f 8 = 87 := by
  have eq1 := hf 8 (show (8 : ℝ) > 0 by norm_num)
  have eq2 := hf (252 : ℝ) (show (252 : ℝ) > 0 by norm_num)
  have eq3 : (2016 / (8 : ℝ) ) = (252 : ℝ) := by norm_num
  have eq4 : (2016 / (252 : ℝ) ) = (8 : ℝ) := by norm_num
  rw [eq3] at eq1
  rw [eq4] at eq2
  norm_num at eq1 eq2
  linarith