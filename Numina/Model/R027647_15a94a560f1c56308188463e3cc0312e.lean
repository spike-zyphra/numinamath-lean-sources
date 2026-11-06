import Mathlib

theorem algebra_8072 (x y : ℤ) (hx : x > 0) (hy : y > 0) :
    x^3 - y^3 = 2 * x * y + 8 ↔ False := by 
  constructor
  · -- Assume x^3 - y^3 = 2 * x * y + 8, prove False
    intro h
    have h1 : x > y := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x^2 - y^2), sq_nonneg (x * y - 4)]
    have h2 : x ≥ y + 1 := by
      linarith
    have h3 : y ≤ 3 := by
      nlinarith [sq_nonneg (x - y - 1), sq_nonneg (x + y), sq_nonneg (x * y - 4), sq_nonneg (x - 3), sq_nonneg (y - 3)]
    have h4 : y ≥ 1 := by
      linarith [show 0 < y from hy]
    have h5 : x ≤ 5 := by
      nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 1), sq_nonneg (y - 3), h3, h4]
    have h6 : x ≥ 1 := by
      linarith [show 0 < x from hx]
    interval_cases y <;> interval_cases x <;> omega
  · -- Assume False, prove anything
    intro h
    cases h