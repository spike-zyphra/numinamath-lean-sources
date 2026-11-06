import Mathlib

theorem inequalities_603090 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    4 ≤ 1 / a + 1 / b + 1 / c + 3 / (a + b + c) := by

  have h2 : 1 / a + 1 / b + 1 / c = (b * c + a * c + a * b) := by
    have ha' : a ≠ 0 := by linarith
    have hb' : b ≠ 0 := by linarith
    have hc' : c ≠ 0 := by linarith
    field_simp [ha', hb', hc', habc]
    <;> nlinarith
  rw [h2] at *
  have h3 : 0 < a + b + c := by
    nlinarith
  have h4 : (b * c + a * c + a * b) + 3 / (a + b + c) ≥ 4 := by
    have h5 : 0 < a + b + c := h3
    have h6 : (b * c + a * c + a * b) + 3 / (a + b + c) - 4 ≥ 0 := by
      have h6 : 0 < (a + b + c) := h3
      have h7 : (b * c + a * c + a * b) + 3 / (a + b + c) - 4 = ((b * c + a * c + a * b) * (a + b + c) + 3 - 4 * (a + b + c)) / (a + b + c) := by
        field_simp
        <;> ring
      rw [h7] at *
      apply div_nonneg
      have h8 : (b * c + a * c + a * b) * (a + b + c) + 3 - 4 * (a + b + c) ≥ 0 := by
        nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (a * c - 1),
                  sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
                  sq_nonneg (a * b * c - 1),
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, habc]
      linarith
      all_goals positivity
    linarith
  linarith