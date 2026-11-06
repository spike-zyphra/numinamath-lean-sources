import Mathlib

theorem algebra_183363 (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (x + y) * 7 = (x ^ 2 - x * y + y ^ 2) * 3) :
    (x = 4 ∧ y = 5) ∨ (x = 5 ∧ y = 4) := by
  have h1 : x^2 ≤ 49 ∧ y^2 ≤ 49 := by
    constructor
    · -- Show x^2 ≤ 49
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 4), sq_nonneg (y - 4), sq_nonneg (x - 5), sq_nonneg (y - 5), sq_nonneg (x + y - 4), sq_nonneg (x + y - 5), sq_nonneg (x * y - 4), sq_nonneg (x * y - 5)]
    · -- Show y^2 ≤ 49
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 4), sq_nonneg (y - 4), sq_nonneg (x - 5), sq_nonneg (y - 5), sq_nonneg (x + y - 4), sq_nonneg (x + y - 5), sq_nonneg (x * y - 4), sq_nonneg (x * y - 5)]
  have h2 : x ≤ 7 := by nlinarith [h1.1]
  have h3 : x ≥ -7 := by nlinarith [h1.1]
  have h4 : y ≤ 7 := by nlinarith [h1.2]
  have h5 : y ≥ -7 := by nlinarith [h1.2]
  interval_cases x <;> interval_cases y
  <;> norm_num at h hx hy
  <;> omega