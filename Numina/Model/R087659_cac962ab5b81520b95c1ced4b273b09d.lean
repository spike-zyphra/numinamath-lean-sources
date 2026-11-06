import Mathlib

theorem inequalities_251622 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a * b + a / b + b / a ≥ 1 + a + b := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < a * b := mul_pos h1 h2
  have h6 : a * b + a / b + b / a - (1 + a + b) ≥ 0 := by
    have h7 : a * b + a / b + b / a - (1 + a + b) = (a^2 * b^2 + a^2 + b^2 - a * b - a^2 * b - a * b^2) / (a * b) := by
      field_simp
      ring
    rw [h7]
    have h8 : a^2 * b^2 + a^2 + b^2 - a * b - a^2 * b - a * b^2 ≥ 0 := by
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a - b), sq_nonneg (a * (b - 1)), sq_nonneg (b * (a - 1)), sq_nonneg (a * b - a), sq_nonneg (a * b - b)]
    have h9 : a * b > 0 := by positivity
    apply div_nonneg
    linarith
    all_goals nlinarith [h1, h2]
  linarith