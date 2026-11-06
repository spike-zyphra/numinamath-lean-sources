import Mathlib

theorem inequalities_600032 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 5 ≤ (b + c - a)^2 / ((b + c)^2 + a^2) +
            (c + a - b)^2 / ((c + a)^2 + b^2) +
            (a + b - c)^2 / ((a + b)^2 + c^2) := by

  have h1 : 0 < (b + c) ^ 2 + a ^ 2 := by positivity
  have h2 : 0 < (c + a) ^ 2 + b ^ 2 := by positivity
  have h3 : 0 < (a + b) ^ 2 + c ^ 2 := by positivity
  have h4 : (b + c - a)^2 / ((b + c)^2 + a^2) +
          (c + a - b)^2 / ((c + a)^2 + b^2) +
          (a + b - c)^2 / ((a + b)^2 + c^2) - 3 / 5 ≥ 0 := by

    have h5 : (b + c - a)^2 / ((b + c)^2 + a^2) +
          (c + a - b)^2 / ((c + a)^2 + b^2) +
          (a + b - c)^2 / ((a + b)^2 + c^2) - 3 / 5 =
          ((b + c - a) ^ 2 * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2) +
          (c + a - b) ^ 2 * ((b + c) ^ 2 + a ^ 2) * ((a + b) ^ 2 + c ^ 2) +
          (a + b - c) ^ 2 * ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2) - 3 / 5 * ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2)) / (( (b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2)) := by
      field_simp
      ring

    rw [h5]
    apply div_nonneg
    · -- Show that the numerator is non-negative
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), sq_nonneg (c * (a - b)), 
          sq_nonneg (a * (b - c)), sq_nonneg (b * (b - c)), sq_nonneg (c * (b - c)), 
          sq_nonneg (a * (a - c)), sq_nonneg (b * (a - c)), sq_nonneg (c * (a - c)), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < c * a by nlinarith), 
          mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith)
        ]
    · -- Show that the denominator is positive
      positivity

  linarith