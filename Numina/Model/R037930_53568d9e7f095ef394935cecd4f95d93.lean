import Mathlib

theorem inequalities_302644 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    1 / (2 * a^2 + b^2 + c^2) +
    1 / (2 * b^2 + c^2 + a^2) +
    1 / (2 * c^2 + a^2 + b^2) ≤ 3 / 4 := by
  have h1 : 0 < a * b * c := by 
    apply mul_pos
    apply mul_pos ha hb
    exact hc
  have h2 : 2 * a^2 + b^2 + c^2 > 0 := by nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
  have h3 : 2 * b^2 + c^2 + a^2 > 0 := by nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
  have h4 : 2 * c^2 + a^2 + b^2 > 0 := by nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
  have h5 : 1 / (2 * a^2 + b^2 + c^2) + 1 / (2 * b^2 + c^2 + a^2) + 1 / (2 * c^2 + a^2 + b^2) - 3 / 4 ≤ 0 := by 
    have h6 : 0 < (2 * a^2 + b^2 + c^2) * (2 * b^2 + c^2 + a^2) * (2 * c^2 + a^2 + b^2) := by positivity
    have h7 : 1 / (2 * a^2 + b^2 + c^2) + 1 / (2 * b^2 + c^2 + a^2) + 1 / (2 * c^2 + a^2 + b^2) - 3 / 4 = 
      ( (2 * b^2 + c^2 + a^2) * (2 * c^2 + a^2 + b^2) + (2 * a^2 + b^2 + c^2) * (2 * c^2 + a^2 + b^2) + (2 * a^2 + b^2 + c^2) * (2 * b^2 + c^2 + a^2) - 3 / 4 * (2 * a^2 + b^2 + c^2) * (2 * b^2 + c^2 + a^2) * (2 * c^2 + a^2 + b^2) ) / ( (2 * a^2 + b^2 + c^2) * (2 * b^2 + c^2 + a^2) * (2 * c^2 + a^2 + b^2) ) := by
      field_simp
      ring
    rw [h7] at *
    have h8 : (2 * b^2 + c^2 + a^2) * (2 * c^2 + a^2 + b^2) + (2 * a^2 + b^2 + c^2) * (2 * c^2 + a^2 + b^2) + (2 * a^2 + b^2 + c^2) * (2 * b^2 + c^2 + a^2) - 3 / 4 * (2 * a^2 + b^2 + c^2) * (2 * b^2 + c^2 + a^2) * (2 * c^2 + a^2 + b^2) ≤ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a + b + c - 3), sq_nonneg (a * b + b * c + c * a - 3), sq_nonneg (a * a - b * b), sq_nonneg (b * b - c * c), sq_nonneg (c * c - a * a), sq_nonneg (a^2 + b^2 + c^2 - 3), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    apply div_nonpos_of_nonpos_of_nonneg h8 (show ( (2 * a^2 + b^2 + c^2) * (2 * b^2 + c^2 + a^2) * (2 * c^2 + a^2 + b^2) ) ≥ 0 by positivity)
  linarith