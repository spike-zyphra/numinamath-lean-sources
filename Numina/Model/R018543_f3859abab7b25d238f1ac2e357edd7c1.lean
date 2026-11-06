import Mathlib

theorem inequalities_236040 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a^4 + b^4 + c^4 - 2 * (a^2 * b^2 + a^2 * c^2 + b^2 * c^2) +
      a^2 * b * c + b^2 * a * c + c^2 * a * b ≥ 0 := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
            sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2), 
            mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc, 
            mul_nonneg (show 0 ≤ a * b from by nlinarith) (show 0 ≤ c from hc), 
            sq_nonneg (a*b - b*c), sq_nonneg (b*c - c*a), sq_nonneg (c*a - a*b),
            mul_nonneg (show 0 ≤ a * b by nlinarith) (show 0 ≤ b * c by nlinarith),
            mul_nonneg (show 0 ≤ a * b by nlinarith) (show 0 ≤ c * a by nlinarith),
            mul_nonneg (show 0 ≤ b * c by nlinarith) (show 0 ≤ c * a by nlinarith)]