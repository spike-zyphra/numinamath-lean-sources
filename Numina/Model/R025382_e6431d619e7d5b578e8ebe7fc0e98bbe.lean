import Mathlib

theorem inequalities_36364 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 3) :
    (a^4 + 3 * a * b^3) / (a^3 + 2 * b^3) + (b^4 + 3 * b * c^3) / (b^3 + 2 * c^3) +
    (c^4 + 3 * c * a^3) / (c^3 + 2 * a^3) ≤ 4 := by

  have h2 : (a^4 + 3 * a * b^3) / (a^3 + 2 * b^3) = a + (a * b^3) / (a^3 + 2 * b^3) := by
    field_simp
    ring
  
  have h3 : (b^4 + 3 * b * c^3) / (b^3 + 2 * c^3) = b + (b * c^3) / (b^3 + 2 * c^3) := by
    field_simp
    ring
  
  have h4 : (c^4 + 3 * c * a^3) / (c^3 + 2 * a^3) = c + (c * a^3) / (c^3 + 2 * a^3) := by
    field_simp
    ring
  
  have h5 : (a * b^3) / (a^3 + 2 * b^3) ≤ b / 3 := by
    have h6 : a^3 + 2 * b^3 ≥ 3 * a * b^2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 2 * b), sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), sq_nonneg (a^2 - b^2), mul_pos ha hb, mul_pos hb ha]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_pos ha hb, mul_pos hb ha]

  have h5' : (b * c^3) / (b^3 + 2 * c^3) ≤ c / 3 := by
    have h6 : b^3 + 2 * c^3 ≥ 3 * b * c^2 := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (b - 2 * c), sq_nonneg (b * (b - c)), sq_nonneg (c * (b - c)), sq_nonneg (b^2 - c^2), mul_pos hb hc, mul_pos hc hb]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_pos hb hc, mul_pos hc hb]

  have h5'' : (c * a^3) / (c^3 + 2 * a^3) ≤ a / 3 := by
    have h6 : c^3 + 2 * a^3 ≥ 3 * c * a^2 := by
      nlinarith [sq_nonneg (c - a), sq_nonneg (c + a), sq_nonneg (c - 2 * a), sq_nonneg (c * (c - a)), sq_nonneg (a * (c - a)), sq_nonneg (c^2 - a^2), mul_pos hc ha, mul_pos ha hc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_pos hc ha, mul_pos ha hc]

  have h7 : a + b + c ≤ 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
              h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  rw [h2, h3, h4]
  linarith [h5, h5', h5'', h7, mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, h]