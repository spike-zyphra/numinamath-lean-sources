import Mathlib

theorem algebra_220858 (x : ℝ) (hx : x ≠ 0) : 1 / x = x ^ (-1 : ℤ) := by 
  simp [zpow_neg_one]