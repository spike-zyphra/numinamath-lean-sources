import Mathlib

theorem inequalities_600089 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 * (a ^ 3 + b ^ 3 + c ^ 3 + a * b * c) ≥ 4 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a - (b + c)), sq_nonneg (b - (a + c)), sq_nonneg (c - (a + b)),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
            sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
            sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]