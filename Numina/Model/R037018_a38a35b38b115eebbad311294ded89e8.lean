import Mathlib

theorem inequalities_152242 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    (a^2 + 9) / (2 * a^2 + (b + c)^2) +
    (b^2 + 9) / (2 * b^2 + (c + a)^2) +
    (c^2 + 9) / (2 * c^2 + (a + b)^2) ≤ 5 := by

  have h1 : b + c = 3 - a := by
    linarith
  have h2 : c + a = 3 - b := by
    linarith
  have h3 : a + b = 3 - c := by
    linarith
  have h4 : (a^2 + 9) / (2 * a^2 + (b + c)^2) ≤ (1 / 3) * a + 4 / 3 := by
    have h1' : b + c = 3 - a := h1
    rw [h1']
    apply (div_le_iff₀ (by nlinarith [sq_nonneg (a), sq_nonneg (3 - a), h])).mpr
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 3), sq_nonneg (a * (a - 1)), sq_nonneg ((3 - a) * (a - 1)), sq_nonneg (a * (3 - a)), mul_pos ha (show 0 < 3 - a from by nlinarith), sq_nonneg (a - 3 / 2)]
  have h5 : (b^2 + 9) / (2 * b^2 + (c + a)^2) ≤ (1 / 3) * b + 4 / 3 := by
    have h2' : c + a = 3 - b := h2
    rw [h2']
    apply (div_le_iff₀ (by nlinarith [sq_nonneg (b), sq_nonneg (3 - b), h])).mpr
    nlinarith [sq_nonneg (b - 1), sq_nonneg (b - 3), sq_nonneg (b * (b - 1)), sq_nonneg ((3 - b) * (b - 1)), sq_nonneg (b * (3 - b)), mul_pos hb (show 0 < 3 - b from by nlinarith), sq_nonneg (b - 3 / 2)]
  have h6 : (c^2 + 9) / (2 * c^2 + (a + b)^2) ≤ (1 / 3) * c + 4 / 3 := by
    have h3' : a + b = 3 - c := h3
    rw [h3']
    apply (div_le_iff₀ (by nlinarith [sq_nonneg (c), sq_nonneg (3 - c), h])).mpr
    nlinarith [sq_nonneg (c - 1), sq_nonneg (c - 3), sq_nonneg (c * (c - 1)), sq_nonneg ((3 - c) * (c - 1)), sq_nonneg (c * (3 - c)), mul_pos hc (show 0 < 3 - c from by nlinarith), sq_nonneg (c - 3 / 2)]
  linarith [h4, h5, h6, h]