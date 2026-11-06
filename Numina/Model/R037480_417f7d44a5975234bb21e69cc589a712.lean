import Mathlib

theorem inequalities_232233 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a * (a^2 + b * c) / (b + c) + b * (b^2 + c * a) / (c + a) +
    c * (c^2 + a * b) / (a + b) ≥ a * b + b * c + c * a := by
  have h1 : 0 < b + c := by linarith
  have h2 : 0 < c + a := by linarith
  have h3 : 0 < a + b := by linarith
  have h4 : a * (a^2 + b * c) / (b + c) + b * (b^2 + c * a) / (c + a) + c * (c^2 + a * b) / (a + b) - (a * b + b * c + c * a) ≥ 0 := by
    have h5 : 0 < (b + c) * (c + a) * (a + b) := by positivity
    have h6 : a * (a^2 + b * c) / (b + c) + b * (b^2 + c * a) / (c + a) + c * (c^2 + a * b) / (a + b) - (a * b + b * c + c * a) = 
        (a * (a^2 + b * c) * (c + a) * (a + b) + b * (b^2 + c * a) * (b + c) * (a + b) + c * (c^2 + a * b) * (b + c) * (c + a) - (a * b + b * c + c * a) * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b)) := by
      field_simp
      ring
    rw [h6] at *
    apply div_nonneg
    · -- Numerator is non-negative.
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), 
          sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), 
            sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), 
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
                mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), 
                  mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
                    mul_pos (show 0 < a * c by nlinarith) (show 0 < b * c by nlinarith)
        ]
    · -- Denominator is positive.
      positivity
  linarith