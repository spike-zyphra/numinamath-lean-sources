import Mathlib

theorem inequalities_137740 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a^2 * b + b^2 * c + c^2 * a) * (a * b^2 + b * c^2 + c * a^2) ≥ 9 * (a * b * c)^2 := by 
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), 
          sq_nonneg (b * (b - a)), sq_nonneg (c * (c - b)), sq_nonneg (c * (c - a)), 
          mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc, 
          mul_nonneg (mul_nonneg ha hb) hc]