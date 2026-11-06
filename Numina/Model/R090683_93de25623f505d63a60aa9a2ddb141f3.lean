import Mathlib

theorem algebra_68397 {a b : ℝ} (h : (a + b + a) * (a + b + b) = 9) : a * b ≤ 1 := by
  have eq1 : 2 * a^2 + 5 * (a * b) + 2 * b^2 = 9 := by
    nlinarith
  
  have h1 : 2 * a^2 + 2 * b^2 ≥ 4 * (a * b) := by
    nlinarith [sq_nonneg (a - b)]

  nlinarith [eq1, h1]