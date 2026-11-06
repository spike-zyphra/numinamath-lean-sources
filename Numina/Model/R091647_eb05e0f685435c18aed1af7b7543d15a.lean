import Mathlib

theorem inequalities_601959 (x y : ℝ) (h : x + y = 1) : x * y ≤ 1 / 4 := by 
  have hy : y = 1 - x := by linarith
  rw [hy]
  have h1 : (x - 1 / 2) ^ 2 ≥ 0 := by 
    apply sq_nonneg
  linarith