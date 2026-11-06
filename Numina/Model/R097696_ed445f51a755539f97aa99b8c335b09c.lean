import Mathlib

theorem inequalities_128083 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a^3 + a < b - b^3) :
    a < 1 ∧ b < 1 ∧ a < b := by
  have h1 : a^3 + b^3 + a < b := by linarith
  have h2 : b < 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2)]
  have h3 : a < 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2)]
  have h4 : a < b := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2)]
  exact ⟨h3, h2, h4⟩