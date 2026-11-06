import Mathlib
theorem inequalities_606059 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 3) : a + b + c ≥ a * b * c + 2 := by
-- use Lagrange multiplier to calculate critical point
-- it turns out that the minimum is obtained when a = b = c = 1
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]