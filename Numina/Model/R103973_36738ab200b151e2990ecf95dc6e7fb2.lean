import Mathlib

theorem algebra_240 {x y : ℤ} (hx : x > 0) (hy : y > 0)
    (h1 : x * y + x + y = 23) (h2 : x ^ 2 * y + x * y ^ 2 = 120) :
    x ^ 2 + y ^ 2 = 34 := by 
  have h3 : x ≤ 23 := by
    nlinarith
  have h4 : y ≤ 23 := by
    nlinarith
  interval_cases x <;> interval_cases y <;> omega