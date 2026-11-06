import Mathlib

theorem inequalities_37789 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : b^3 + b ≤ a - a^3) :
    b < a ∧ a < 1 ∧ a^2 + b^2 < 1 := by
  have h1 : b < a := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1),
      pow_two_nonneg (a - 1), pow_two_nonneg (b - 1),
      mul_pos ha hb, sq_nonneg (a - b)]
  have h2 : a < 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1),
      sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1),
      pow_two_nonneg (a - 1), pow_two_nonneg (b - 1),
      mul_pos ha hb, sq_nonneg (a - b)]
  have h3 : a^2 + b^2 < 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1),
      sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1),
      pow_two_nonneg (a - 1), pow_two_nonneg (b - 1),
      mul_pos ha hb, sq_nonneg (a - b)]
  constructor
  · exact h1
  constructor
  · exact h2
  · exact h3