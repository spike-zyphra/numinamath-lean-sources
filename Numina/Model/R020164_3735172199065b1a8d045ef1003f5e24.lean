import Mathlib

theorem inequalities_69694 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a ^ 2 + b ^ 2) / (2 * a ^ 5 * b ^ 5) + 81 * a ^ 2 * b ^ 2 / 4 + 9 * a * b > 18 := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < a ^ 2 * b ^ 2 := by positivity
  have h3 : 0 < a ^ 5 * b ^ 5 := by positivity

  have h4 : (a ^ 2 + b ^ 2) / (2 * a ^ 5 * b ^ 5) + 81 * a ^ 2 * b ^ 2 / 4 + 9 * a * b - 18 > 0 := by
    have h4 : ( (a ^ 2 + b ^ 2) / (2 * a ^ 5 * b ^ 5) + 81 * a ^ 2 * b ^ 2 / 4 + 9 * a * b - 18 ) =
        ( 2 * (a ^ 2 + b ^ 2) + 81 * (a ^ 7 * b ^ 7) + 36 * (a ^ 6 * b ^ 6) - 72 * (a ^ 5 * b ^ 5) ) / (4 * a ^ 5 * b ^ 5) := by
      field_simp
      ring
    rw [h4] at *
    have h7 : 2 * (a ^ 2 + b ^ 2) + 81 * (a ^ 7 * b ^ 7) + 36 * (a ^ 6 * b ^ 6) - 72 * (a ^ 5 * b ^ 5) > 0 := by
      nlinarith [sq_nonneg (a ^ 3 * b ^ 3 - a ^ 2 * b ^ 2), sq_nonneg (a ^ 3 * b ^ 3 - a * b), sq_nonneg (a * b - 1), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a ^ 3 - b ^ 3), sq_nonneg (a * b), sq_nonneg (a * b - 1), sq_nonneg (a ^ 2 * b ^ 2 - 1 / 9), sq_nonneg (a ^ 2 * b ^ 2), sq_nonneg (a^2 - b^2), sq_nonneg (a - b), mul_pos ha hb, mul_pos (show 0 < a ^ 2 by positivity) (show 0 < b ^ 2 by positivity), sq_nonneg (a ^ 3 * b ^ 3 - 1 / 9), sq_nonneg (a ^ 3 * b ^ 3 - a * b), sq_nonneg (a ^ 3 * b ^ 3 - a ^ 2 * b ^ 2), sq_nonneg (a ^ 2 * b ^ 2 - a * b), sq_nonneg (a * b - 1), sq_nonneg (a * b - 2 / 3), sq_nonneg (a * b - 1 / 3), sq_nonneg (a ^ 3 * b ^ 3 - 2 / 3), sq_nonneg (a ^ 3 * b ^ 3 - 1 / 9) ]
    have h8 : ( 2 * (a ^ 2 + b ^ 2) + 81 * (a ^ 7 * b ^ 7) + 36 * (a ^ 6 * b ^ 6) - 72 * (a ^ 5 * b ^ 5) ) / (4 * a ^ 5 * b ^ 5) > 0 := by
      apply div_pos
      linarith
      positivity
    linarith

  linarith