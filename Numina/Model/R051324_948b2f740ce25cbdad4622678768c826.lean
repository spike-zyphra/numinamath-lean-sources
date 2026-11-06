import Mathlib

theorem inequalities_277214 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 9 := by
  have h1 : a * b * c > 0 := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : (a + b + c) * (1 / a + 1 / b + 1 / c) - 9 ≥ 0 := by
    have h3 : (a + b + c) * (1 / a + 1 / b + 1 / c) - 9 =
        ((a + b + c) * (a * b + a * c + b * c) - 9 * a * b * c) / (a * b * c) := by
      field_simp
      ring
    rw [h3]
    have h4 : (a + b + c) * (a * b + a * c + b * c) - 9 * a * b * c ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h5 : a * b * c > 0 := h1
    have h6 : ((a + b + c) * (a * b + a * c + b * c) - 9 * a * b * c) / (a * b * c) ≥ 0 := by
      apply div_nonneg
      linarith
      positivity
    linarith
  linarith