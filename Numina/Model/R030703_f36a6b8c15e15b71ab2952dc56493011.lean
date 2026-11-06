import Mathlib

theorem inequalities_155499 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (1 + a / b) ^ 2 + (1 + b / a) ^ 2 ≥ 8 := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : (1 + a / b) ^ 2 + (1 + b / a) ^ 2 - 8 ≥ 0 := by
    have pos1 : 0 < a := ha
    have pos2 : 0 < b := hb
    have pos3 : 0 < a * b := h1
    have pos4 : 0 < a ^ 2 * b ^ 2 := by positivity
    have h3 : (1 + a / b) ^ 2 + (1 + b / a) ^ 2 - 8 =
        ( (a + b) ^ 2 * (a^2 + b^2) - 8 * (a^2 * b^2) ) / (a^2 * b^2) := by
      field_simp
      ring
    rw [h3] at *
    apply div_nonneg
    have h4 : (a + b) ^ 2 * (a^2 + b^2) - 8 * (a^2 * b^2) ≥ 0 := by
      nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a - b), sq_nonneg (a * b - a * b), sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a * (a - b)), sq_nonneg (b * (b - a)), mul_pos ha hb, mul_pos ha (show 0 < b * b by positivity), mul_pos (show 0 < a * a by positivity) hb, sq_nonneg (a^2 + b^2 - 2 * a * b)]
    linarith
    positivity
  linarith