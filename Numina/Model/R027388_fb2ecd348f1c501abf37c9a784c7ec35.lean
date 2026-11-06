import Mathlib

theorem inequalities_232230 (a : ℝ) : |a - 1| ≤ a ^ 2 - a + 1 := by
  cases le_or_lt 0 (a - 1) with
  | inl h =>
    have h1 : |a - 1| = a - 1 := by
      rw [abs_of_nonneg]
      linarith
    rw [h1]
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]
  | inr h =>
    have h1 : |a - 1| = (1 - a : ℝ) := by
      rw [abs_of_neg]
      linarith
      all_goals linarith
    rw [h1]
    nlinarith [sq_nonneg (a), sq_nonneg (a - 1)]