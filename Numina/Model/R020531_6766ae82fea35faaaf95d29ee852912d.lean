import Mathlib

theorem inequalities_283709 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a^4 + b^4 + c^4 - 2*(a^2*b^2 + a^2*c^2 + b^2*c^2) +
      a^2*b*c + b^2*a*c + c^2*a*b ≥ 0 := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2),
            sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc,
            sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (a - b - c), sq_nonneg (a + b + c),
            sq_nonneg (a * (b - c)), sq_nonneg (b * (a - c)), sq_nonneg (c * (a - b)),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
            sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
            sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
            mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith),
            mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c by linarith),
            mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith)
          ]