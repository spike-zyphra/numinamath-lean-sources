import Mathlib

theorem algebra_156122 (y : ℝ → ℝ) (hy : y = fun x => x ^ 6) :
    y 0 = 0 := by
  rw [hy]
  norm_num