import Mathlib

theorem inequalities_601094 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    5 / 3 ≤ a / (b + c) + b / (c + a) + c / (a + b) + a * b * c / (2 * (a^3 + b^3 + c^3)) := by

  have h1 : 0 < (b + c) * (c + a) * (a + b) * (2 * (a^3 + b^3 + c^3)) := by positivity
  
  have h2 : a / (b + c) + b / (c + a) + c / (a + b) + a * b * c / (2 * (a^3 + b^3 + c^3)) - 5 / 3 ≥ 0 := by
  
    have h4 : a / (b + c) + b / (c + a) + c / (a + b) + a * b * c / (2 * (a^3 + b^3 + c^3)) - 5 / 3 =
      (3 * a * (c + a) * (a + b) * (2 * (a^3 + b^3 + c^3)) + 3 * b * (b + c) * (a + b) * (2 * (a^3 + b^3 + c^3)) + 3 * c * (b + c) * (c + a) * (2 * (a^3 + b^3 + c^3)) + 3 * (a * b * c) * (b + c) * (c + a) * (a + b) - 5 * (b + c) * (c + a) * (a + b) * (2 * (a^3 + b^3 + c^3))) / (3 * (b + c) * (c + a) * (a + b) * (2 * (a^3 + b^3 + c^3))) := by
      field_simp
      ring
    
    rw [h4] at *
  
    apply div_nonneg
  
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
        sq_nonneg (a^3 - b^3), sq_nonneg (a^3 - c^3), sq_nonneg (b^3 - c^3),
        pow_two_nonneg (a - b), pow_two_nonneg (a - c), pow_two_nonneg (b - c)]
  
    positivity
  
  linarith