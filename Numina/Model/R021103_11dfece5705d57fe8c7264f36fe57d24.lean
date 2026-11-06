import Mathlib

theorem inequalities_127069 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hord : a ≥ b ∧ b ≥ c) (hsum : a + b + c ≤ 1) :
    a^2 + 3 * b^2 + 5 * c^2 ≤ 1 := by
  nlinarith [sq_nonneg (a + b + c - 1), sq_nonneg (a - b), sq_nonneg (b - c),
          sq_nonneg (a + b + c - 1), hord.1, hord.2, mul_pos ha hb, mul_pos hb hc, 
          mul_pos ha hc]