import Mathlib

theorem algebra_975 {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (h1 : a + b + c = 0) (h2 : a * b * c < 0) :
    0 < 1 / a + 1 / b + 1 / c := by
  have h3 : 1 / a + 1 / b + 1 / c = (b * c + a * c + a * b) / (a * b * c) := by
    field_simp [ha, hb, hc]
    ring
  rw [h3] at *
  have h4 : b * c + a * c + a * b < 0 := by
    have h5 : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (b * c + a * c + a * b) := by ring
    rw [show a + b + c = (0 : ℚ) by exact h1] at h5
    have h6 : a ^ 2 + b ^ 2 + c ^ 2 > 0 := by
      have ha2 : a ^ 2 > 0 := by
        exact sq_pos_of_ne_zero ha
      have hb2 : b ^ 2 > 0 := by
        exact sq_pos_of_ne_zero hb
      have hc2 : c ^ 2 > 0 := by
        exact sq_pos_of_ne_zero hc
      linarith
    linarith
  have h7 : a * b * c < 0 := h2
  apply div_pos_of_neg_of_neg
  · -- Show that b*c + a*c + a*b < 0
    linarith [h4]
  · -- Show that a * b * c < 0
    linarith [h7]