import Mathlib

theorem inequalities_601831 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^2 + b^2)^2 ≥ (a + b + c) * (a + b - c) * (b + c - a) * (c + a - b) := by
  nlinarith [sq_nonneg (a^2 + b^2 - c^2), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (a^2 + b^2 - 2*a*b), 
          sq_nonneg (a^2 - b^2 + c^2 - 2*a*c), sq_nonneg (b^2 + c^2 - 2*b*c), 
          sq_nonneg (c^2 - (a-b)^2), sq_nonneg (a^2+b^2), sq_nonneg (c^2 - a^2 - b^2 + 2*a*b)]