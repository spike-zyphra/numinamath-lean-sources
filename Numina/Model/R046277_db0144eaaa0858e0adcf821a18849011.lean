import Mathlib

theorem algebra_721 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a = b / 2) (h2 : 1 / a + 1 / b = 1 / 12) (h3 : 1 / b * 9 = 1 - 1 / a * 18):
    1 / a * 18 = 18 := by
  have hb2 : b = 2 * a := by
    linarith
  have h4 : 1 / a + 1 / b = 1 / 12 := h2
  rw [hb2] at h4
  have ha2 : a ≠ 0 := by
    nlinarith
  field_simp at h4 h3
  all_goals nlinarith [sq_nonneg (a * 1), sq_nonneg (b * 1)]