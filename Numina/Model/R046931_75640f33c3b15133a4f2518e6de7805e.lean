import Mathlib

theorem inequalities_8438 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
  a^3 + b^3 + c^3 + 6*a*b*c ≥ (1/4)*(a+b+c)^3 := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
          mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]