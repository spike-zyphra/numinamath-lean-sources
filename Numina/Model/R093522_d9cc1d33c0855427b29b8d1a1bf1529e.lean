import Mathlib

theorem inequalities_6619 (a : ℝ) (ha : a ≥ 1) :
    4 * a^3 - 9 * a^2 + 9 * a + 4 ≥ 0 := by 
  have h1 : a - 1 ≥ 0 := by linarith 
  nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 2), sq_nonneg (a - 3 / 2), sq_nonneg (a - 1 / 2), sq_nonneg (a + 1)]