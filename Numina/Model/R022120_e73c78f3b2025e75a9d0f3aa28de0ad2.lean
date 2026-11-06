import Mathlib

theorem inequalities_30654 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a * b + b * c + c * a = 1) :
    1 / a + 1 / b + 1 / c ≥ 3 * (a + b + c) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith

  have h2 : 1 / a + 1 / b + 1 / c - 3 * (a + b + c) ≥ 0 := by
    have h3 : 0 < a * b * c := h1

    have h4 : (1 / a + 1 / b + 1 / c - 3 * (a + b + c)) = ( (a * b + b * c + c * a) - 3 * (a + b + c) * (a * b * c) ) / (a * b * c) := by
      field_simp
      ring
    rw [h4] at *
    have h5 : (a * b + b * c + c * a) - 3 * (a + b + c) * (a * b * c) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

    apply div_nonneg
    linarith
    all_goals nlinarith

  linarith