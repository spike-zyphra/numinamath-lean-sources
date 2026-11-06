import Mathlib

theorem algebra_13480 (rate_marg : ℝ) (hrate_marg : rate_marg * 2.4 = 100) :
    rate_marg * 3 = 125 := by
  have h : rate_marg = (100 : ℝ) / 2.4 := by
    linarith
  rw [h]
  norm_num