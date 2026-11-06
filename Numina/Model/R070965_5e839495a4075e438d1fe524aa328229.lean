import Mathlib

open Real

theorem inequalities_154764 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a^4 + b^4 + c^4 ≤ 2*(a^2*b^2 + b^2*c^2 + c^2*a^2)) :
    a^2 + b^2 + c^2 ≤ 2*(a*b + b*c + c*a) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b + c - a), sq_nonneg (a + b + c - b), sq_nonneg (a + b + c - c),
          sq_nonneg (a*b - b*c), sq_nonneg (b*c - c*a), sq_nonneg (c*a - a*b),
          mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]