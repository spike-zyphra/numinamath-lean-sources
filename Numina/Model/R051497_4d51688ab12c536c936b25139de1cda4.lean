import Mathlib

open Real

theorem algebra_221121 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b)) / (a^3 + b^3 + c^3 - 2 * a * b * c) ≤ 6 := by 
  have pos : a^3 + b^3 + c^3 - 2 * a * b * c > 0 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
      sq_nonneg (a^2), sq_nonneg (b^2), sq_nonneg (c^2)]
  have h1 : a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) - 6 * (a^3 + b^3 + c^3 - 2 * a * b * c) ≤ 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * a - b * b), sq_nonneg (b * b - c * c), sq_nonneg (c * c - a * a),
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h2 : a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) ≤ 6 * (a^3 + b^3 + c^3 - 2 * a * b * c) := by linarith 
  apply (div_le_iff₀ pos).mpr 
  linarith