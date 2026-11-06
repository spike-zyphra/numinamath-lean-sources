import Mathlib

theorem algebra_2468 (a : ℝ) : -|a| ≤ 0 := by 
  have h : |a| ≥ 0 := abs_nonneg a
  linarith