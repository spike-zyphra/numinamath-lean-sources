import Mathlib

theorem algebra_240649 {x y : ℤ} (hx : x > 0) (hy : y > 0)
    (h : y * x ^ 2 + x * y ^ 2 = 70) : x ^ 4 + y ^ 4 = 641 := by
  have h1 : x ≤ 10 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x * y), h, mul_pos hx hy]
  have h2 : y ≤ 10 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x * y), h, mul_pos hx hy]
  interval_cases x <;> interval_cases y
  <;> omega