import Mathlib

theorem algebra_306182 {a b : ℝ} (h : a^4 + b^4 = a^2 - 2 * a^2 * b^2 + b^2 + 6) : a^2 + b^2 = 3 := by
  have h1 : (a^2 + b^2)^2 - (a^2 + b^2) - 6 = 0 := by
    nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a * b)]
  -- Factor the quadratic equation
  have h2 : (a^2 + b^2 - 3) * (a^2 + b^2 + 2) = 0 := by
    nlinarith [h1]
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Solve the case where a^2 + b^2 - 3 = 0
    linarith
  · -- Show contradiction in the case where a^2 + b^2 + 2 = 0
    nlinarith [sq_nonneg a, sq_nonneg b]