import Mathlib

theorem inequalities_227470 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^2 / (a + b)) + (b^2 / (b + c)) ≥ (3 * a + 2 * b - c) / 4 := by
  have h1 : 0 < a + b := by linarith
  have h2 : 0 < b + c := by linarith
  have h3 : (a ^ 2 / (a + b) + b ^ 2 / (b + c)) - (3 * a + 2 * b - c) / 4 ≥ 0 := by
    have hfrac1 : (a ^ 2 / (a + b) + b ^ 2 / (b + c)) - (3 * a + 2 * b - c) / 4 =
      (4 * a ^ 2 * (b + c) + 4 * b ^ 2 * (a + b) - (3 * a + 2 * b - c) * (a + b) * (b + c)) / (4 * (a + b) * (b + c)) := by
      field_simp
      ring
    rw [hfrac1]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
      sq_nonneg (a * b - b * c), sq_nonneg (a * b - a * c), sq_nonneg (a * c - b * c)]
    all_goals positivity
  linarith