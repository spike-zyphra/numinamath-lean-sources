import Mathlib

theorem algebra_200167 (k : ℤ) (x y : ℤ)
    (h1 : x^2 + k * y^2 = 4) (h2 : k * x^2 - y^2 = 2) :
    (x = 1 ∧ y = 1) ∨ (x = 1 ∧ y = -1) ∨ (x = -1 ∧ y = 1) ∨ (x = -1 ∧ y = -1) := by
  have h3 : x^4 + y^4 -4*x^2 + 2*y^2 =0 := by
    nlinarith [sq_nonneg (k), sq_nonneg (x * y), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (y - 1), sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (y + 1)]

  have h4 : x ≤ 2 := by nlinarith [sq_nonneg (x - 2), sq_nonneg (y ^ 2), sq_nonneg (x ^ 2 - 2), sq_nonneg (y ^2 -1)]
  have h5 : x ≥ -2 := by nlinarith [sq_nonneg (x + 2), sq_nonneg (y ^ 2), sq_nonneg (x ^ 2 - 2), sq_nonneg (y ^2 -1)]
  have h6 : y ≤ 2 := by nlinarith [sq_nonneg (y - 2), sq_nonneg (x ^ 2), sq_nonneg (y ^ 2 -1), sq_nonneg (x ^ 2 - 2)]
  have h7 : y ≥ -2 := by nlinarith [sq_nonneg (y + 2), sq_nonneg (x ^ 2), sq_nonneg (y ^2 -1), sq_nonneg (x ^2 - 2)]
  interval_cases x <;> interval_cases y <;> omega