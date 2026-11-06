import Mathlib

theorem algebra_317920 {a b : ℝ} (h : a^3 + b^3 + 3 * a * b = 1) : a + b = 1 ∨ a + b = -2 := by
  have h1 : (a + b - 1) * ((a + b) ^ 2 + (a + b) + 1 - 3 * a * b) = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1), sq_nonneg (a + b + 2), sq_nonneg (a - 1), sq_nonneg (b - 1)]
  cases' (mul_eq_zero.1 h1) with h2 h3
  · -- case h2: a + b - 1 = 0
    left
    linarith
  · -- case h3: (a + b) ^ 2 + (a + b) + 1 - 3 * a * b = 0
    right
    have h4 : (a + b + 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (a - b), sq_nonneg (a * (b) - 1), sq_nonneg (a + b + 2)]
    have h5 : a + b + 2 = 0 := by
      nlinarith
    linarith