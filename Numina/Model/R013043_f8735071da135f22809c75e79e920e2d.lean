import Mathlib

theorem inequalities_225394 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (9 * b + 4 * c) / (11 * a ^ 2) + (9 * c + 4 * a) / (11 * b ^ 2) +
    (9 * a + 4 * b) / (11 * c ^ 2) ≥ 1 / a + 1 / b + 1 / c := by
  have h1 : (9 * b + 4 * c) / (11 * a ^ 2) + (9 * c + 4 * a) / (11 * b ^ 2) + (9 * a + 4 * b) / (11 * c ^ 2) - (1 / a + 1 / b + 1 / c) ≥ 0 := by 
    have pos1 : 0 < a * b * c := by positivity
    have term1 : ((9 * b + 4 * c) / (11 * a ^ 2) + (9 * c + 4 * a) / (11 * b ^ 2) + (9 * a + 4 * b) / (11 * c ^ 2) - (1 / a + 1 / b + 1 / c)) =
      ((9 * b + 4 * c) * (b ^ 2 * c ^ 2) + (9 * c + 4 * a) * (a ^ 2 * c ^ 2) + (9 * a + 4 * b) * (a ^ 2 * b ^ 2) - 11 * a * b^2 * c^2 - 11 * a^2 * b * c^2 - 11 * a^2 * b^2 * c) / (11 * a^2 * b^2 * c^2) := by 
      field_simp 
      ring 
    rw [term1] at *
    apply div_nonneg 
    -- Prove Numerator is non-negative.
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (a * b - c * a), sq_nonneg (b * c - c * a), 
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), 
      sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), 
      sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos (show 0 < a * b from by nlinarith) (show 0 < b * c from by nlinarith), 
      mul_pos (show 0 < a * b from by nlinarith) (show 0 < a * c from by nlinarith), 
      mul_pos (show 0 < b * c from by nlinarith) (show 0 < a * c from by nlinarith)
    ]
    -- Prove Denominator is positive.
    positivity 
  linarith [h1]