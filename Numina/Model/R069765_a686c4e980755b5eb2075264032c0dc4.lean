import Mathlib

theorem inequalities_598151
    (a b c : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c) :
    (a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c * a + a^2) ≥ (a * b + b * c + c * a)^3 := by 
  have h1 : a * b ≥ 0 := mul_nonneg ha hb
  have h2 : b * c ≥ 0 := mul_nonneg hb hc
  have h3 : c * a ≥ 0 := mul_nonneg hc ha
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha, 
          sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a)]