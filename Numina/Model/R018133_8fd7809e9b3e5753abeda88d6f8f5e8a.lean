import Mathlib

theorem inequalities_99410 (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (hb : 0 < b)
    (hord : a ≥ b ∧ b ≥ c) :
    b / a + c / b + a / c ≥ (1 / 3) * (a + b + c) * (1 / a + 1 / b + 1 / c) := by

  rcases hord with ⟨h1, h2⟩
  have h4 : b / a + c / b + a / c - (1 / 3) * (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 0 := by
    have h3 : 0 < a * b * c := by
      positivity
    have h5 : b / a + c / b + a / c - (1 / 3) * (a + b + c) * (1 / a + 1 / b + 1 / c) =
      (3 * (b ^ 2 * c + a * c ^ 2 + a ^ 2 * b) - (a + b + c) * (a * b + a * c + b * c)) / (3 * a * b * c) := by
      field_simp
      ring
    rw [h5] at *
    apply div_nonneg
    · -- Show that the numerator is non-negative
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
                sq_nonneg (a * (a - b)), sq_nonneg (a * (b - c)), sq_nonneg (a * (a - c)), 
                sq_nonneg (b * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (b * (a - c)), 
                sq_nonneg (c * (a - b)), sq_nonneg (c * (b - c)), sq_nonneg (c * (a - c)), 
                mul_nonneg (show 0 ≤ a - b by linarith) (show 0 ≤ b - c by linarith), 
                mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), 
                mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c by linarith), 
                mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith)
              ]
    · -- Show that the denominator is positive
      positivity
  linarith [h4]