import Mathlib

theorem inequalities_211666 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a^2 < b) (h2 : b^2 < c) (h3 : c^2 < a) : a < 1 ∧ b < 1 ∧ c < 1 := by
  have h4 : a < 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h5 : b < 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h6 : c < 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  exact ⟨h4, h5, h6⟩