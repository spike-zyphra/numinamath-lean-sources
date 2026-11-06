import Mathlib

theorem inequalities_599562 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    9 ≤ 1 / a + 1 / b + 1 / c := by
  have h2 : 1 / a + 1 / b + 1 / c - 9 ≥ 0 := by
    have h3 : 1 / a + 1 / b + 1 / c - 9 =
        (b * c + a * c + a * b - 9 * a * b * c) / (a * b * c) := by
      field_simp [show 0 < a by linarith, show 0 < b by linarith, show 0 < c by linarith]
      ring
    rw [h3]
    have h4 : 0 < a * b * c := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h5 : b * c + a * c + a * b - 9 * a * b * c ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a - 1/3), sq_nonneg (b - 1/3), sq_nonneg (c - 1/3),
          h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    have h6 : (b * c + a * c + a * b - 9 * a * b * c) / (a * b * c) ≥ 0 := by
      apply div_nonneg
      linarith
      positivity
    linarith
  linarith