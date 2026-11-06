import Mathlib

theorem inequalities_46108
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (habc : a * b * c = 8) :
    6 ≤ (a * b + 4) / (a + 2) + (b * c + 4) / (b + 2) + (c * a + 4) / (c + 2) := by
  have h3 : 0 < a + 2 := by
    linarith
  have h4 : 0 < b + 2 := by
    linarith
  have h5 : 0 < c + 2 := by
    linarith

  have h3' : (a * b + 4) / (a + 2) + (b * c + 4) / (b + 2) + (c * a + 4) / (c + 2) - 6 ≥ 0 := by
    have h3a : 0 < (a + 2) * (b + 2) * (c + 2) := by
      positivity
    have h3b : ((a * b + 4) / (a + 2) + (b * c + 4) / (b + 2) + (c * a + 4) / (c + 2) - 6) =
      ((a * b + 4) * (b + 2) * (c + 2) + (b * c + 4) * (a + 2) * (c + 2) + (c * a + 4) * (a + 2) * (b + 2) - 6 * (a + 2) * (b + 2) * (c + 2)) / ((a + 2) * (b + 2) * (c + 2)) := by
      field_simp
      ring
    have h3c : ((a * b + 4) * (b + 2) * (c + 2) + (b * c + 4) * (a + 2) * (c + 2) + (c * a + 4) * (a + 2) * (b + 2) - 6 * (a + 2) * (b + 2) * (c + 2)) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - 4), sq_nonneg (b * c - 4), sq_nonneg (c * a - 4), 
          sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2),
          sq_nonneg (a * b * c - 8),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
    have h3d : ((a * b + 4) * (b + 2) * (c + 2) + (b * c + 4) * (a + 2) * (c + 2) + (c * a + 4) * (a + 2) * (b + 2) - 6 * (a + 2) * (b + 2) * (c + 2)) / ((a + 2) * (b + 2) * (c + 2)) ≥ 0 := by 
      apply div_nonneg
      linarith
      all_goals positivity
    linarith [h3b, h3d]
  linarith