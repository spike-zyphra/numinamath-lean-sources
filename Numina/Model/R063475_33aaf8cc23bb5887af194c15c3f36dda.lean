import Mathlib

theorem algebra_127413 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a^2 = b^2 + b * c) (h2 : b^2 = c^2 + a * c) :
    1 / c = 1 / a + 1 / b := by
  have h3 : a * b = c * (a + b) := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
  have h4 : 1 / c = 1 / a + 1 / b := by
    have h5 : a * b = c * (a + b) := h3
    have h6 : a ≠ 0 := by nlinarith
    have h7 : b ≠ 0 := by nlinarith
    have h8 : c ≠ 0 := by nlinarith
    field_simp [h6, h7, h8]
    nlinarith
  exact h4