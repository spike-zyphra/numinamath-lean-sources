import Mathlib

theorem number_theory_4885 (k a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a ^ k * b ^ k = (a * b) ^ k := by 
  rw [← Real.mul_rpow]
  all_goals nlinarith