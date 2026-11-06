import Mathlib

theorem inequalities_222821 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (1 + 1 / a) * (1 + 1 / b) ≥ 8 / (1 + a * b) := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < 1 + a * b := by
    nlinarith [h1]
  have h3 : (1 + 1 / a) * (1 + 1 / b) - 8 / (1 + a * b) ≥ 0 := by
    have h4 : 0 < a * b * (1 + a * b) := by
      positivity
    have h5 : (1 + 1 / a) * (1 + 1 / b) - 8 / (1 + a * b) =
      ((a + 1) * (b + 1) * (1 + a * b) - 8 * (a * b)) / (a * b * (1 + a * b)) := by
      field_simp
      <;> ring
    rw [h5] at *
    apply div_nonneg
    · -- Show that the numerator is non-negative.
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a - 1), sq_nonneg (b - 1),
        sq_nonneg (a * b), sq_nonneg (a - b),
          mul_pos ha hb, mul_pos (show 0 < a by linarith) (show 0 < b by linarith), mul_pos (show 0 < a * b by nlinarith) (show 0 < 1 + a * b by nlinarith)
        ]
    · -- Show that the denominator is positive.
      positivity
  linarith