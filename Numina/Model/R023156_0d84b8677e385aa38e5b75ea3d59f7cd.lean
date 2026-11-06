import Mathlib

theorem inequalities_105130 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 8) :
    6 ≤ (a * b + 4) / (a + 2) + (b * c + 4) / (b + 2) + (c * a + 4) / (c + 2) := by
  have h1 : a + 2 > 0 := by linarith
  have h2 : b + 2 > 0 := by linarith
  have h3 : c + 2 > 0 := by linarith

  have h4 : (a * b + 4) / (a + 2) + (b * c + 4) / (b + 2) + (c * a + 4) / (c + 2) - 6 ≥ 0 := by
    have pos1 : (a + 2) * (b + 2) * (c + 2) > 0 := by positivity
    have h5 : (a * b + 4) / (a + 2) + (b * c + 4) / (b + 2) + (c * a + 4) / (c + 2) - 6 =
        ((a * b + 4) * (b + 2) * (c + 2) + (b * c + 4) * (a + 2) * (c + 2) + (c * a + 4) * (a + 2) * (b + 2) - 6 * (a + 2) * (b + 2) * (c + 2)) / ((a + 2) * (b + 2) * (c + 2)) := by
      field_simp [h1, h2, h3]
      ring
    rw [h5] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - 4), sq_nonneg (b * c - 4), sq_nonneg (c * a - 4),
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc 
        ]
    · -- Show denominator is positive
      positivity

  linarith