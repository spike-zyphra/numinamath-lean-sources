import Mathlib

theorem inequalities_33765 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (h1 : a * b * c = 1000) (h2 : b * c * (1 - a) + a * (b + c) = 110) (h3 : a < 1) :
    10 < c ∧ c < 100 := by
  have h4 : b * c + a * (b + c) = 1110 := by
    have eq1 : b * c * (1 - a) + a * (b + c) = 110 := h2
    have eq2 : a * b * c = 1000 := h1
    nlinarith [eq1, eq2]
  constructor
  · -- Show that 10 < c
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b * c - 100), sq_nonneg (c - 10), h1, h4, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  · -- Show that c < 100
    nlinarith [sq_nonneg (a * b - 100), sq_nonneg (c - 100), sq_nonneg (a - 1), sq_nonneg (b * c - 100), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, h1, h4, mul_pos (show 0 < a by linarith) (show 0 < b * c by nlinarith [mul_pos hb hc])]