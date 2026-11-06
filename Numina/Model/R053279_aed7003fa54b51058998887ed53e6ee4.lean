import Mathlib

theorem algebra_234794 {x y : ℝ} (hx : x = 1) (hy : y = 1 / 2) :
    (x - y) ^ 2 + (y - 2 * Real.sqrt x + 2) ^ 2 = 1 / 2 := by 
  rw [hx, hy]
  have hsqrt1 : Real.sqrt (1 : ℝ) = 1 := by
    rw [Real.sqrt_eq_cases]
    norm_num
  rw [hsqrt1]
  norm_num