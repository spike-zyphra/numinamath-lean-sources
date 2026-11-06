import Mathlib

theorem inequalities_1838 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^3 + b^3 + c^3 + 3 * a * b * c) / ((a + b) * (b + c) * (c + a)) +
    (a + b + c)^2 / (6 * (a^2 + b^2 + c^2)) ≥ 5 / 4 := by 
  have h1 : (a + b) * (b + c) * (c + a) > 0 := by 
    positivity
  have h2 : 6 * (a^2 + b^2 + c^2) > 0 := by 
    positivity

  have h3 : (a^3 + b^3 + c^3 + 3 * a * b * c) / ((a + b) * (b + c) * (c + a)) + 
    (a + b + c)^2 / (6 * (a^2 + b^2 + c^2)) - 5 / 4 ≥ 0 := by 
    have h' : (a^3 + b^3 + c^3 + 3 * a * b * c) / ((a + b) * (b + c) * (c + a)) + (a + b + c)^2 / (6 * (a^2 + b^2 + c^2)) - 5 / 4 = 
      (24 * (a^2 + b^2 + c^2) * (a^3 + b^3 + c^3 + 3 * a * b * c) + 4 * (a + b + c)^2 * (a + b) * (b + c) * (c + a) - 5 * 6 * (a + b) * (b + c) * (c + a) * (a^2 + b^2 + c^2)) / (4 * 6 * (a + b) * (b + c) * (c + a) * (a^2 + b^2 + c^2)) := by 
      field_simp
      ring
    rw [h']
    apply div_nonneg 
    · -- Show that the numerator is non-negative 
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                  sq_nonneg (a * (a - b) ), sq_nonneg (a * (a - c) ), sq_nonneg (b * (b - c) ), sq_nonneg (b * (b - a) ), sq_nonneg (c * (c - a) ), sq_nonneg (c * (c - b) ), 
                  sq_nonneg (a * b + b * c + c * a - a^2 - b^2 - c^2), sq_nonneg (a + b + c - 2 * a), sq_nonneg (a + b + c - 2 * b), sq_nonneg (a + b + c - 2 * c),
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc 
                ]
    · -- Show that the denominator is non-negative
      positivity
  
  linarith