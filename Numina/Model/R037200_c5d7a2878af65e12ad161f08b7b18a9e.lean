import Mathlib

theorem inequalities_28846 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a + b + c) * (a * b + b * c + c * a) + 3 ≥ 4 * (a + b + c) := by

  have h1 : 0 < a * b := by nlinarith
  have h2 : 0 < a * c := by nlinarith 
  have h3 : 0 < b * c := by nlinarith

  have h4 : (a + b + c) * (a * b + b * c + c * a) + 3 ≥ 4 * (a + b + c) := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a + b + c - 3), sq_nonneg (a * b + b * c + c * a - 3), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  exact h4