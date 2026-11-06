import Mathlib

theorem algebra_319487 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a + b + c = 0) (h2 : a * b * c > 0) :
    1 / a + 1 / b + 1 / c < 0 := by

  have h3 : 1 / a + 1 / b + 1 / c = (a * b + a * c + b * c) / (a * b * c) := by
    field_simp [ha, hb, hc]
    ring

  have h4 : a * b + a * c + b * c < 0 := by
    have h5 : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2 * (a * b + a * c + b * c) := by
      nlinarith

    rw [show a + b + c = 0 by linarith] at h5
    have h6 : a ^ 2 + b ^ 2 + c ^ 2 > 0 := by
      have ha2 : a^2 > 0 := by
        exact sq_pos_of_ne_zero ha
      have hb2 : b^2 > 0 := by
        exact sq_pos_of_ne_zero hb
      have hc2 : c^2 > 0 := by
        exact sq_pos_of_ne_zero hc
      linarith

    nlinarith

  rw [h3]
  have h7 : (a * b + a * c + b * c) / (a * b * c) < 0 := by
    apply div_neg_of_neg_of_pos
    linarith
    all_goals linarith

  linarith