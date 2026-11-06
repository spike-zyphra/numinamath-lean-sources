import Mathlib

theorem inequalities_308560 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) +
    (2 * b + a + c)^2 / (2 * b^2 + (a + c)^2) +
    (2 * c + a + b)^2 / (2 * c^2 + (a + b)^2) ≤ 8 := by 
  have h2 : 0 < 2 * a^2 + (b + c)^2 := by
    positivity
  have h3 : 0 < 2 * b^2 + (a + c)^2 := by
    positivity
  have h4 : 0 < 2 * c^2 + (a + b)^2 := by
    positivity
  have h5 : (2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) +
          (2 * b + a + c)^2 / (2 * b^2 + (a + c)^2) +
          (2 * c + a + b)^2 / (2 * c^2 + (a + b)^2) - 8 ≤ 0 := by
    have h6 : 0 < (2 * a^2 + (b + c)^2) * (2 * b^2 + (a + c)^2) * (2 * c^2 + (a + b)^2) := by positivity
    have h7 : (2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) +
            (2 * b + a + c)^2 / (2 * b^2 + (a + c)^2) +
            (2 * c + a + b)^2 / (2 * c^2 + (a + b)^2) - 8 =
            ((2 * a + b + c)^2 * (2 * b^2 + (a + c)^2) * (2 * c^2 + (a + b)^2) +
            (2 * b + a + c)^2 * (2 * a^2 + (b + c)^2) * (2 * c^2 + (a + b)^2) +
            (2 * c + a + b)^2 * (2 * a^2 + (b + c)^2) * (2 * b^2 + (a + c)^2) - 8 * (2 * a^2 + (b + c)^2) * (2 * b^2 + (a + c)^2) * (2 * c^2 + (a + b)^2)) / ((2 * a^2 + (b + c)^2) * (2 * b^2 + (a + c)^2) * (2 * c^2 + (a + b)^2)) := by
      field_simp
      ring
    rw [h7]
    apply div_nonpos_of_nonpos_of_nonneg
    -- Show the numerator is non-positive.
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (b - c)), sq_nonneg (a * (c - a)), 
      sq_nonneg (b * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (b * (c - a)), 
      sq_nonneg (c * (a - b)), sq_nonneg (c * (b - c)), sq_nonneg (c * (c - a)), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
      mul_pos (show 0 < a * c by nlinarith) (show 0 < b * c by nlinarith)]
    all_goals positivity
  linarith