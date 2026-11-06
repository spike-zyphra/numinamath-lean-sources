import Mathlib

theorem algebra_144908 (x y : ℕ) (hx : x < 10) (hy : y < 10)
    (h : 2^x * 9^y = 2000 + 100 * x + 10 * 9 + y) :
    x^2 * y^3 = 200 := by
  interval_cases x <;> interval_cases y <;> omega