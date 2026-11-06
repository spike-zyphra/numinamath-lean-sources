import Mathlib

theorem number_theory_126327 (x y : ℤ) : ¬(x^2 + y^2 = 175) := by
  rintro h
  have h1 : x ≤ 13 := by nlinarith [sq_nonneg y, h]
  have h2 : x ≥ -14 := by nlinarith [sq_nonneg y, h]
  have h3 : y ≤ 13 := by nlinarith [sq_nonneg x, h]
  have h4 : y ≥ -14 := by nlinarith [sq_nonneg x, h]
  interval_cases x <;> interval_cases y
  <;> omega