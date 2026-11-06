import Mathlib

theorem inequalities_602983 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a * b / (a^5 + b^5 + a * b) +
    b * c / (b^5 + c^5 + b * c) +
    c * a / (c^5 + a^5 + c * a) ≤ 1 := by

  have h1 : a^5 + b^5 ≥ a^2 * b^2 * (a + b) := by
    nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a - b), sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), sq_nonneg (a * (a^2 - b^2)), sq_nonneg (b * (a^2 - b^2)), sq_pos_of_pos ha, sq_pos_of_pos hb, mul_pos ha hb]
  have h3 : a * b / (a^5 + b^5 + a * b) ≤ 1 / (a * b * (a + b) + 1) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h1, sq_nonneg (a * b - 1), sq_nonneg (a - b), sq_nonneg (a^2 - b^2)]
  have h4 : b^5 + c^5 ≥ b^2 * c^2 * (b + c) := by
    nlinarith [sq_nonneg (b^2 - c^2), sq_nonneg (b - c), sq_nonneg (b * (b - c)), sq_nonneg (c * (b - c)), sq_nonneg (b * (b^2 - c^2)), sq_nonneg (c * (b^2 - c^2)), sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos hb hc]
  have h6 : b * c / (b^5 + c^5 + b * c) ≤ 1 / (b * c * (b + c) + 1) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h4, sq_nonneg (b * c - 1), sq_nonneg (b - c), sq_nonneg (b^2 - c^2)]
  have h7 : c^5 + a^5 ≥ c^2 * a^2 * (c + a) := by
    nlinarith [sq_nonneg (c^2 - a^2), sq_nonneg (c - a), sq_nonneg (c * (c - a)), sq_nonneg (a * (c - a)), sq_nonneg (c * (c^2 - a^2)), sq_nonneg (a * (c^2 - a^2)), sq_pos_of_pos hc, sq_pos_of_pos ha, mul_pos hc ha]
  have h9 : c * a / (c^5 + a^5 + c * a) ≤ 1 / (c * a * (c + a) + 1) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h7, sq_nonneg (c * a - 1), sq_nonneg (c - a), sq_nonneg (c^2 - a^2)]
  have h10 : 1 / (a * b * (a + b) + 1) + 1 / (b * c * (b + c) + 1) + 1 / (c * a * (c + a) + 1) = 1 := by
    have h11 : c = 1 / (a * b) := by
      field_simp
      <;> nlinarith [habc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    rw [h11]
    field_simp
    <;> nlinarith [mul_pos ha hb, mul_pos ha (show 0 < 1 / (a * b) by apply one_div_pos.mpr (by positivity)), sq_nonneg (a * b - 1), sq_nonneg (b * (1 / (a * b)) - 1), sq_nonneg ((1 / (a * b)) * a - 1)]
  linarith [h3, h6, h9, h10]