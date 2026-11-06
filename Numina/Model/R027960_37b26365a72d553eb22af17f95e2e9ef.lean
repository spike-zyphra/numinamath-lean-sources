import Mathlib

theorem inequalities_179239 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    (a + 1 / a) * (b + 1 / b) * (c + 1 / c) ≥ 1000 / 27 := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : (a + 1 / a) * (b + 1 / b) * (c + 1 / c) - 1000 / 27 ≥ 0 := by
    have h3 : (a + 1 / a) * (b + 1 / b) * (c + 1 / c) - 1000 / 27 =
        ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) - 1000 / 27 * (a * b * c)) / (a * b * c) := by
      field_simp
      ring
    rw [h3]
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - 1 / 9), sq_nonneg (a * c - 1 / 9), sq_nonneg (b * c - 1 / 9),
      sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 3),
      h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    all_goals
      positivity
  linarith [h2]
  all_goals positivity