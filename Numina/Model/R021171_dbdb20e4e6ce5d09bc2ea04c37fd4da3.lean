import Mathlib

theorem inequalities_155931 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 ≥ 25 / 2 := by
  have h1 : b = 1 - a := by linarith
  rw [h1]
  have h2 : a > 0 := ha
  have h3 : (1 - a) > 0 := by nlinarith
  have h4 : a ^ 2 * (1 - a) ^ 2 > 0 := by positivity
  have h5 : (a + 1 / a) ^ 2 + ((1 - a) + 1 / (1 - a)) ^ 2 - 25 / 2 ≥ 0 := by
    have h6 : (a + 1 / a) ^ 2 + ((1 - a) + 1 / (1 - a)) ^ 2 - 25 / 2 =
        ( (a^2 + 1)^2 * (1 - a)^2 + ((1 - a)^2 + 1)^2 * a^2 - (25 / 2) * a^2 * (1 - a)^2 ) / (a^2 * (1 - a)^2) := by
      field_simp [(show a ≠ 0 by linarith), (show (1 - a : ℝ) ≠ 0 by nlinarith)]
      ring
    rw [h6] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg ((1 - a) - 1 / 2), sq_nonneg (a * (1 - a) - 1 / 4),
        sq_nonneg (a - 1 / 2), sq_nonneg ((1 - a) - 1 / 2), sq_nonneg (a^2 - (1 - a)^2),
        sq_nonneg (a^2 - 1), sq_nonneg ((1 - a)^2 - 1),
        mul_pos ha (show (0 : ℝ) < 1 - a by nlinarith), mul_pos (show (0 : ℝ) < 1 - a by nlinarith) (show (0 : ℝ) < 1 by linarith)]
    positivity
  linarith [h5]