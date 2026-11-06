import Mathlib

theorem algebra_18581 {x : ℝ} (hx : x > 18) (h : Real.logb 5 (x - 18) = 2) : x = 43 := by
  have h1 : x - 18 > 0 := by
    linarith
  have h2 : x - 18 = (5:ℝ) ^ (2:ℝ) := by
    rw [Real.logb_eq_iff_rpow_eq] at h
    all_goals
      linarith
  norm_num at h2
  linarith