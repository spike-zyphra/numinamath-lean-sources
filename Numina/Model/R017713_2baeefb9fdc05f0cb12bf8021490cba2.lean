import Mathlib

theorem inequalities_90291 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a + b + c + 3 / (a * b + b * c + c * a) ≥ 4 := by
  have h1 : 0 < a * b + b * c + c * a := by
    positivity
  have h2 : a * b + b * c + c * a > 0 := by
    positivity
  have h3 : a + b + c + 3 / (a * b + b * c + c * a) - 4 ≥ 0 := by
    have h4 : a * b + b * c + c * a > 0 := by positivity
    have h5 : (a + b + c + 3 / (a * b + b * c + c * a) - 4) = ((a + b + c) * (a * b + b * c + c * a) + 3 - 4 * (a * b + b * c + c * a)) / (a * b + b * c + c * a) := by
      field_simp
      ring
    rw [h5]
    apply div_nonneg
    nlinarith [sq_nonneg (a + b + c - 3), sq_nonneg (a * b + b * c + c * a - 3), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
              sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
              mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc]
    positivity
  linarith