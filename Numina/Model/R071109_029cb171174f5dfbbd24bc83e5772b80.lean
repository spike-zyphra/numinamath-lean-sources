import Mathlib

theorem inequalities_598666 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^3 + b^3 + c^3 ≥ a^2 * b + b^2 * c + c^2 * a := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a - (b + c)/2), sq_nonneg (b - (a + c)/2), sq_nonneg (c - (a + b)/2),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]