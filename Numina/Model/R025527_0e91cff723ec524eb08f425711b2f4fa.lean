import Mathlib

theorem inequalities_596972 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a^4 + b^4 + c^4 - 2*(a^2*b^2+b^2*c^2+c^2*a^2) +
    a^2*b*c + b^2*c*a + c^2*a*b ≥ 0 := by 
  nlinarith [sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (-a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), 
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (b * (a - c)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), sq_nonneg (c * (b - a)), 
          mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]