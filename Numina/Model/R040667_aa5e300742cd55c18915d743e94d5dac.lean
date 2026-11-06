import Mathlib

theorem algebra_325684 (x : ℝ) (hx : 6 * x ^ 4 - 13 * x ^ 3 + 12 * x ^ 2 - 13 * x + 6 = 0) :
    x = 2 / 3 ∨ x = 3 / 2 := by
  have h1 : 6 * x ^ 4 - 13 * x ^ 3 + 12 * x ^ 2 - 13 * x + 6 = 0 := hx
  have h2 : (x ^ 2 + 1) * (6 * x ^ 2 - 13 * x + 6) = 0 := by
    nlinarith [h1]
  cases' (mul_eq_zero.1 h2) with h3 h4
  · -- Case where x^2 + 1 = 0, which is impossible for real numbers
    have h5 : x ^ 2 + 1 = 0 := by linarith
    nlinarith [sq_nonneg x]
  · -- Case where 6 * x^2 - 13 * x + 6 = 0
    have h5 : 6 * x ^ 2 - 13 * x + 6 = 0 := by linarith
    have h6 : (x - 2 / 3) * (x - 3 / 2) = 0 := by
      nlinarith [h5]
    cases' (mul_eq_zero.1 h6) with h7 h8
    · -- Case where x - 2/3 = 0
      left
      linarith
    · -- Case where x - 3/2 = 0
      right
      linarith