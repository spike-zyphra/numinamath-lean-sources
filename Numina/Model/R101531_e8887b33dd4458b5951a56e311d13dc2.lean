import Mathlib

theorem algebra_9782 (x : ℤ) (hx : 0 < x) (h : x^3 + 11 * x^2 = 135 * x + 1177) : x = 11 := by
  have h1 : x^3 + 11 * x^2 - 135 * x - 1177 = 0 := by linarith
  have h2 : (x - 11) * (x^2 + 22 * x + 107) = 0 := by
    nlinarith [h1]

  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case where x - 11 = 0, so x = 11
    linarith
  · -- Case where x^2 + 22 * x + 107 = 0
    have : x < 0 := by 
      nlinarith [sq_nonneg (x), sq_nonneg (x + 11), sq_nonneg (x * 11), sq_nonneg (x ^ 2 + 22 * x)]
    linarith