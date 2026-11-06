import Mathlib

theorem algebra_203631
  {a b c : ℝ}
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hc : c ≠ 0)
  (h1 : a + b + c = 0)
  (h2 : 1 / a + 1 / b + 1 / c = 1) :
  a * b * c < 0 := by
  have h3 : a * b + b * c + c * a = a * b * c := by
    field_simp [ha, hb, hc] at h2 ⊢
    nlinarith [h2]
  have h4 : (a + b + c) ^ 2 = 0 := by
    rw [h1]
    all_goals norm_num
  have h5 : a ^ 2 + b ^ 2 + c ^ 2 = -2 * (a * b * c) := by
    have h6 : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by
      ring
    rw [h4] at h6
    have h7 : a * b + b * c + c * a = a * b * c := h3
    rw [h7] at h6
    linarith
  have h8 : a ^ 2 + b ^ 2 + c ^ 2 > 0 := by
    have ha2 : a ^ 2 > 0 := by
      exact sq_pos_of_ne_zero ha
    have hb2 : b ^ 2 > 0 := by
      exact sq_pos_of_ne_zero hb
    have hc2 : c ^ 2 > 0 := by
      exact sq_pos_of_ne_zero hc
    linarith
  linarith