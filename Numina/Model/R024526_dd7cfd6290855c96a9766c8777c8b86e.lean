import Mathlib

theorem inequalities_220775 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b + c = 1) :
    (a^4 + b^4) / (a^6 + b^6) + (b^4 + c^4) / (b^6 + c^6) +
    (c^4 + a^4) / (c^6 + a^6) ≤ 1 / (a * b * c) := by
  have h1 : (a^4 + b^4) / (a^6 + b^6) ≤ 1 / (a * b) := by
    have h2 : 0 < a^6 + b^6 := by positivity
    have h3 : 0 < a * b := by positivity
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a - b), sq_nonneg (a * b),
      sq_nonneg (a^3 - b^3), sq_nonneg (a^4 - b^4),
      sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)),
      mul_pos ha hb, sq_nonneg (a^2 * b - a * b^2)]
  have h2 : (b^4 + c^4) / (b^6 + c^6) ≤ 1 / (b * c) := by
    have h4 : 0 < b^6 + c^6 := by positivity
    have h5 : 0 < b * c := by positivity
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (b^2 - c^2), sq_nonneg (b - c), sq_nonneg (b * c),
      sq_nonneg (b^3 - c^3), sq_nonneg (b^4 - c^4),
      sq_nonneg (b * (b - c)), sq_nonneg (c * (b - c)),
      mul_pos hb hc, sq_nonneg (b^2 * c - b * c^2)]
  have h3 : (c^4 + a^4) / (c^6 + a^6) ≤ 1 / (c * a) := by
    have h6 : 0 < c^6 + a^6 := by positivity
    have h7 : 0 < c * a := by positivity
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (c^2 - a^2), sq_nonneg (c - a), sq_nonneg (c * a),
      sq_nonneg (c^3 - a^3), sq_nonneg (c^4 - a^4),
      sq_nonneg (c * (c - a)), sq_nonneg (a * (c - a)),
      mul_pos hc ha, sq_nonneg (c^2 * a - c * a^2)]
  have h4 : (a^4 + b^4) / (a^6 + b^6) + (b^4 + c^4) / (b^6 + c^6) + (c^4 + a^4) / (c^6 + a^6) ≤
      1 / (a * b) + 1 / (b * c) + 1 / (c * a) := by
    linarith [h1, h2, h3]
  have h5 : (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) = 1 / (a * b * c) * (a + b + c) := by
    field_simp
    <;> nlinarith
  have h6 : (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) = 1 / (a * b * c) := by
    rw [h5]
    rw [hsum]
    all_goals norm_num
  linarith [h4, h6]