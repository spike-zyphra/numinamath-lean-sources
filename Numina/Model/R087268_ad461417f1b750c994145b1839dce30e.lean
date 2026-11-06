import Mathlib

theorem algebra_1421 (v : ℝ → ℝ) (h : v = fun x => x * 15 / 60) :
  v 4 = 1 := by 
  rw [h]
  norm_num