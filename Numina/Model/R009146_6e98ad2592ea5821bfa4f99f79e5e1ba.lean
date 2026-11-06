import Mathlib

theorem algebra_29045 (yao_tall : ℝ) (yao_tall_in : ℝ) (hoop : ℝ)
    (h : yao_tall = 7 * 12 + 5) (h' : hoop = 10 * 12) :
    hoop - yao_tall = 31 := by
  rw [h] at *
  rw [h']
  norm_num