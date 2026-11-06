import Mathlib

theorem inequalities_172240 (a b : ℝ) (h : (a > 0 ∧ b > 0) ∨ (a < 0 ∧ b < 0)) :
    5 * a^2 - 6 * a * b + 5 * b^2 > 0 := by
  rcases h with h1 | h2
  · -- Case 1: a > 0 and b > 0
    have ha : a > 0 := h1.1
    have hb : b > 0 := h1.2
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_pos_of_pos ha, sq_pos_of_pos hb, mul_pos ha hb]
  · -- Case 2: a < 0 and b < 0
    have ha : a < 0 := h2.1
    have hb : b < 0 := h2.2
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_pos_of_neg ha, sq_pos_of_neg hb, mul_pos_of_neg_of_neg ha hb]