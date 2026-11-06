import Mathlib

theorem inequalities_110622 (a b : ℝ) (h₀ : 0 < b) (h₁ : b < a) :
    a^4 + b^4 > 2 * a * b^3 := by
  have h2 : 0 < a - b := by linarith
  have h3 : a > 0 := by linarith
  have h5 : a^4 + b^4 - 2 * a * b^3 > 0 := by
    nlinarith [sq_pos_of_pos (show 0 < a - b by linarith),
          sq_pos_of_pos (show 0 < b by linarith),
          sq_nonneg (a - b - b),
          sq_nonneg (a + b),
          sq_nonneg (a - b),
          sq_nonneg (a^2 - b^2),
          sq_nonneg (a^2 - b * a),
          sq_nonneg ((a - b) * (a - b)),
          mul_pos (show 0 < a - b by linarith) (show 0 < b by linarith),
          h₁, h₀,
          sq_nonneg (a^2 - b^2),
          sq_pos_of_pos (show 0 < a by linarith)
         ]
  linarith