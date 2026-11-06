import Mathlib

theorem inequalities_599236
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 9 := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : (a + b + c) * (1 / a + 1 / b + 1 / c) - 9 ≥ 0 := by
    have h3 : (a + b + c) * (1 / a + 1 / b + 1 / c) - 9 = ((a + b + c) * (b * c + a * c + a * b) - 9 * (a * b * c)) / (a * b * c) := by
      field_simp
      <;> ring
    rw [h3]
    have h4 : ((a + b + c) * (b * c + a * c + a * b) - 9 * (a * b * c)) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c),
                sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
                mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h5 : (a * b * c) > 0 := h1
    apply div_nonneg
    linarith [h4]
    all_goals linarith [h5]
  linarith [h2]