import Mathlib

theorem inequalities_52174 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a ^ 2 + b ^ 2 + c ^ 2 ≤ 3) :
    (a + b + c) * (a + b + c - a * b * c) ≥ 2 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc, 
          mul_nonneg (show 0 ≤ 3 - a^2 - b^2 - c^2 by nlinarith) (show 0 ≤ 3 by nlinarith)]