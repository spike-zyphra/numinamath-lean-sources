import Mathlib

theorem algebra_1720 {a b : ℝ} (ha : a ≠ b) (y : ℝ → ℝ) (hy : y = fun x => a + b - x) :
    y 0 = a + b := by 
  rw [hy]
  all_goals norm_num