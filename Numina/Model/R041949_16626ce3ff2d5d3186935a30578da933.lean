import Mathlib

theorem inequalities_601583 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a^4 + b^4 + c^4 - 2*(a^2 * b^2 + a^2 * c^2 + b^2 * c^2) +
    a^2 * b * c + b^2 * a * c + c^2 * a * b ≥ 0 := by
  nlinarith [sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (-a + b + c), sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), 
          sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), 
          sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), 
          mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc, 
          mul_nonneg (mul_nonneg ha hb) (mul_nonneg ha hc), 
          mul_nonneg (mul_nonneg ha hb) (mul_nonneg hb hc), 
          mul_nonneg (mul_nonneg ha hc) (mul_nonneg hb hc)
      ]