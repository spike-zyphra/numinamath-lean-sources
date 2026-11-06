import Mathlib

theorem inequalities_209196 (a b c : ℝ) (ha : 0 < c) (hc : c ≤ b) (hb : b ≤ a) :
    (a^2 - b^2) / c + (c^2 - b^2) / a + (a^2 - c^2) / b ≥ 3 * a - 4 * b + c := by

  have h1 : 0 < a := by
    have h2 : 0 < c := by linarith
    have h3 : c ≤ b := by linarith
    have h4 : b ≤ a := by linarith
    nlinarith

  have h2 : 0 < b := by
    have h3 : 0 < c := by linarith
    have h4 : c ≤ b := by linarith
    nlinarith

  have h3 : 0 < a * b * c := by
    positivity

  have h4 : (a^2 - b^2) / c + (c^2 - b^2) / a + (a^2 - c^2) / b - (3 * a - 4 * b + c) ≥ 0 := by
    have h5 : 0 < a * b * c := h3
    have h6 : (a^2 - b^2) / c + (c^2 - b^2) / a + (a^2 - c^2) / b - (3 * a - 4 * b + c) =
        ((a^2 - b^2) * (a * b) + (c^2 - b^2) * (b * c) + (a^2 - c^2) * (a * c) - (3 * a - 4 * b + c) * (a * b * c)) / (a * b * c) := by
      field_simp
      ring
    rw [h6] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)),
          sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)),
          mul_nonneg (show (0 : ℝ) ≤ a - b by nlinarith) (show (0 : ℝ) ≤ b - c by nlinarith),
          mul_nonneg (show (0 : ℝ) ≤ a - b by nlinarith) (show (0 : ℝ) ≤ c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ b - c by nlinarith) (show (0 : ℝ) ≤ c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ a by nlinarith) (show (0 : ℝ) ≤ b - c by nlinarith),
          mul_nonneg (show (0 : ℝ) ≤ a by nlinarith) (show (0 : ℝ) ≤ c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ b by nlinarith) (show (0 : ℝ) ≤ c by linarith)
        ]
    all_goals
      positivity
  linarith