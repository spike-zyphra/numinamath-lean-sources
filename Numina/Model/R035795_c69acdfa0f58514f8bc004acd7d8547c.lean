import Mathlib

theorem inequalities_44127 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a^3 + b^3 + c^3 + 6*a*b*c ≥ (a + b + c)^3 / 4 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (-a + b + c),
          mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]