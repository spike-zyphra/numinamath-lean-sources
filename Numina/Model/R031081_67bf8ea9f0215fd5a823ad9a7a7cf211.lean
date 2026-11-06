import Mathlib

theorem inequalities_111593 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (a + b) + 1 / (b + c) + 1 / (c + a) ≤ (a ^ 2 + b ^ 2 + c ^ 2) / 2 := by

  have h2 : 0 < (a + b) * (b + c) * (c + a) := by
    positivity
  have h3 : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) - (a ^ 2 + b ^ 2 + c ^ 2) / 2 ≤ 0 := by
    have pos1 : 0 < (a + b) * (b + c) * (c + a) := h2
    have h4 : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) - (a ^ 2 + b ^ 2 + c ^ 2) / 2 =
          (2 * (b + c) * (c + a) + 2 * (a + b) * (c + a) + 2 * (a + b) * (b + c) - (a ^ 2 + b ^ 2 + c ^ 2) * (a + b) * (b + c) * (c + a)) / (2 * (a + b) * (b + c) * (c + a)) := by
      field_simp
      ring
    rw [h4] at *
    have h6 : 2 * (b + c) * (c + a) + 2 * (a + b) * (c + a) + 2 * (a + b) * (b + c) - (a ^ 2 + b ^ 2 + c ^ 2) * (a + b) * (b + c) * (c + a) ≤ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc]
    have h7 : (2 * (b + c) * (c + a) + 2 * (a + b) * (c + a) + 2 * (a + b) * (b + c) - (a ^ 2 + b ^ 2 + c ^ 2) * (a + b) * (b + c) * (c + a)) / (2 * (a + b) * (b + c) * (c + a)) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · linarith
      · positivity
    linarith
  linarith [h3]