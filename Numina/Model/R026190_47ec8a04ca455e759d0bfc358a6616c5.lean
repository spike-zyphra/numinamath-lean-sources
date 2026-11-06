import Mathlib

theorem inequalities_600494 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ((2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) +
     (a + 2 * b + c)^2 / (2 * b^2 + (c + a)^2) +
     (a + b + 2 * c)^2 / (2 * c^2 + (a + b)^2)) ≤ 8 := by

  have h1 : ((2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) +
    (a + 2 * b + c)^2 / (2 * b^2 + (c + a)^2) +
    (a + b + 2 * c)^2 / (2 * c^2 + (a + b)^2)) - 8 ≤ 0 := by

    have h9 : ((2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) +
      (a + 2 * b + c)^2 / (2 * b^2 + (c + a)^2) +
      (a + b + 2 * c)^2 / (2 * c^2 + (a + b)^2) ) - 8 =
      ((2 * a + b + c)^2 * (2 * b^2 + (c + a)^2) * (2 * c^2 + (a + b)^2) +
      (a + 2 * b + c)^2 * (2 * a^2 + (b + c)^2) * (2 * c^2 + (a + b)^2) +
      (a + b + 2 * c)^2 * (2 * a^2 + (b + c)^2) * (2 * b^2 + (c + a)^2) 
      - 8 * (2 * a^2 + (b + c)^2) * (2 * b^2 + (c + a)^2) * (2 * c^2 + (a + b)^2)) / ((2 * a^2 + (b + c)^2) * (2 * b^2 + (c + a)^2) * (2 * c^2 + (a + b)^2)) := by 
      field_simp
      ring

    rw [h9] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is ≤ 0 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), sq_nonneg (c * (a - b)), 
          sq_nonneg (a * (a - c)), sq_nonneg (b * (a - c)), sq_nonneg (c * (a - c)), 
          sq_nonneg (a * (b - c)), sq_nonneg (b * (b - c)), sq_nonneg (c * (b - c)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
          mul_pos (show 0 < a * c by nlinarith) (show 0 < b * c by nlinarith)
      ]
    all_goals positivity
  linarith