import Mathlib

theorem inequalities_48744
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hsum : a + b + c = 1) :
    1 / a + 1 / b + 1 / c ≥ 9 := by
  have h1 : 1 / a + 1 / b + 1 / c - 9 ≥ 0 := by
    have h2 : 1 / a + 1 / b + 1 / c - 9 = (b * c + a * c + a * b - 9 * a * b * c) / (a * b * c) := by
      field_simp
      ring
    rw [h2]
    have h3 : b * c + a * c + a * b ≥ 9 * a * b * c := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                sq_nonneg (a - 1/3), sq_nonneg (b - 1/3), sq_nonneg (c - 1/3),
                hsum, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h4 : b * c + a * c + a * b - 9 * a * b * c ≥ 0 := by linarith
    have h5 : a * b * c > 0 := mul_pos (mul_pos ha hb) hc
    apply div_nonneg
    linarith
    all_goals linarith
  linarith