import Mathlib

theorem inequalities_66627 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2*(a^3 + b^3 + c^3 + a*b*c) ≥ (a+b)*(b+c)*(c+a) := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (-a + b + c),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]