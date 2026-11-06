import Mathlib

theorem inequalities_601763 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + 2 * b = 1) :
    1 / a + 2 / b ≥ 9 := by
  have h1 : 0 < a * b := by
    apply mul_pos
    all_goals linarith
  have h2 : 1 / a + 2 / b - 9 ≥ 0 := by
    have h3 : 1 / a + 2 / b - 9 = ((1 / a + 2 / b) * (a + 2 * b) - 9) := by
      have h4 : a + 2 * b = 1 := h
      rw [h4]
      field_simp
      <;> nlinarith
    rw [h3]
    have h5 : (1 / a + 2 / b) * (a + 2 * b) - 9 ≥ 0 := by
      have h6 : (1 / a + 2 / b) * (a + 2 * b) - 9 =
        (2 * (a - b) ^ 2) / (a * b) := by
        field_simp
        nlinarith
      rw [h6]
      have h7 : 2 * (a - b) ^ 2 ≥ 0 := by
        nlinarith [sq_nonneg (a - b)]
      apply div_nonneg
      linarith
      linarith [show 0 < a * b by nlinarith]
    linarith
  linarith