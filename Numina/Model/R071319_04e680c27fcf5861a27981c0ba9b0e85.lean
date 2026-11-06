import Mathlib

theorem algebra_322976 (x y : ℤ) (hx : x > 0) (hy : y > 0)
    (h : 2*x^2+y^2-2*x*y-4*x-30=0) :
    (x=5 ∧ y=10) ∨ (x=7 ∧ y=4) ∨ (x=7 ∧ y=10) := by 
  have h1 : (x - y) ^ 2 + (x - 2) ^ 2 = 34 := by
    nlinarith

  have h2 : x ≤ 12 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2)]

  have h3 : y ≤ 17 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2)]

  interval_cases x <;> interval_cases y <;> omega