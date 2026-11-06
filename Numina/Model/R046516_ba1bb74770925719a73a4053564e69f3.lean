import Mathlib

theorem inequalities_326083 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 4) :
    a / (a ^ 3 + 8) + b / (b ^ 3 + 8) + c / (c ^ 3 + 8) + d / (d ^ 3 + 8) ≤ 4 / 9 := by
  have h1 : a / (a ^ 3 + 8) ≤ (2 * a + 1) / 27 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a ^ 2 - 2), sq_nonneg (a + 2), sq_nonneg (a * (a - 1)), sq_nonneg ((a - 1) * (a ^ 2 + 1)), sq_nonneg ((a) * (a - 1)), mul_pos ha (show 0 < a ^ 2 by positivity)]
  have h2 : b / (b ^ 3 + 8) ≤ (2 * b + 1) / 27 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (b - 1), sq_nonneg (b ^ 2 - 2), sq_nonneg (b + 2), sq_nonneg (b * (b - 1)), sq_nonneg ((b - 1) * (b ^ 2 + 1)), sq_nonneg ((b) * (b - 1)), mul_pos hb (show 0 < b ^ 2 by positivity)]
  have h3 : c / (c ^ 3 + 8) ≤ (2 * c + 1) / 27 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (c - 1), sq_nonneg (c ^ 2 - 2), sq_nonneg (c + 2), sq_nonneg (c * (c - 1)), sq_nonneg ((c - 1) * (c ^ 2 + 1)), sq_nonneg ((c) * (c - 1)), mul_pos hc (show 0 < c ^ 2 by positivity)]
  have h4 : d / (d ^ 3 + 8) ≤ (2 * d + 1) / 27 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (d - 1), sq_nonneg (d ^ 2 - 2), sq_nonneg (d + 2), sq_nonneg (d * (d - 1)), sq_nonneg ((d - 1) * (d ^ 2 + 1)), sq_nonneg ((d) * (d - 1)), mul_pos hd (show 0 < d ^ 2 by positivity)]
  have h5 : a / (a ^ 3 + 8) + b / (b ^ 3 + 8) + c / (c ^ 3 + 8) + d / (d ^ 3 + 8) ≤ (2 * a + 1) / 27 + (2 * b + 1) / 27 + (2 * c + 1) / 27 + (2 * d + 1) / 27 := by
    linarith [h1, h2, h3, h4]
  have h6 : (2 * a + 1) / 27 + (2 * b + 1) / 27 + (2 * c + 1) / 27 + (2 * d + 1) / 27 = 4 / 9 := by
    have h1 : a + b + c + d = 4 := h
    field_simp
    nlinarith [h1]
  linarith [h5, h6]