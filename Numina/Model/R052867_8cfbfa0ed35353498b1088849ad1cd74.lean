import Mathlib

theorem number_theory_11792 (x y : ℤ) (hx : x > 0) (hy : y > 0)
    (h : x^2 + 7 * y^2 = 2011) :
    (x, y) = (38, 9) := by
  have h1 : x ≤ 44 := by nlinarith
  have h2 : y ≤ 18 := by nlinarith
  interval_cases x <;> interval_cases y <;> norm_num at h <;> tauto