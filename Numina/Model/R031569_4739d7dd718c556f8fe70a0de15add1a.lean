import Mathlib

theorem algebra_146 {a b : ℝ} (ha : a ^ 3 - 3 * a ^ 2 + 5 * a = 1) (hb : b ^ 3 - 3 * b ^ 2 + 5 * b = 5) : a + b = 2 := by
  have eq1 : a ^ 3 - 3 * a ^ 2 + 5 * a - 1 = 0 := by linarith
  have eq2 : b ^ 3 - 3 * b ^ 2 + 5 * b - 5 = 0 := by linarith
  have h2 : b = 2 - a := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a + b - 2), sq_nonneg (a - b), sq_nonneg ((a - 1) + (b - 1))]
  have h3 : a + b = 2 := by
    linarith [h2]
  exact h3