import Mathlib

theorem algebra_15274 (x : ℝ) (hx : x ≠ 0) (h : 4 * x - 15 = 20 - 3 * x) :
    (4 * x - 15)^2 = 25 := by
  have eq1 : 7 * x = 35 := by
    linarith
  have hx5 : x = 5 := by
    linarith
  have h1 : 4 * x - 15 = 5 := by
    rw [hx5]
    norm_num
  rw [h1]
  norm_num