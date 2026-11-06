import Mathlib

theorem algebra_5305 {x y : ℤ} (hx : 0 < x) (hy : 0 < y)
    (h : x + x * y - 2 * y = 5) : x * y = 6 := by 
  have eq1 : x * (1 + y) = 5 + 2 * y := by
    linarith 
  have h2 : x ≤ 5 := by 
    nlinarith [h, sq_nonneg (x - 3), sq_nonneg (y - 2), mul_pos hx hy]
  interval_cases x <;> omega