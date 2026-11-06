import Mathlib

theorem algebra_14742 {f : ℝ → ℝ} (h : ∀ x, f (2^x) + x * f (2^(-x)) = 1) :
    f 2 = 0 := by 
  have eq1 := h 1
  have eq2 := h (-1)
  norm_num [show (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) by norm_num, show (2 : ℝ) ^ (-1 : ℝ) = (1 / 2 : ℝ) by norm_num] at eq1 eq2
  linarith