import Mathlib

theorem inequalities_311764 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    5 ≤ (a^3 + b) / (a * (b + c)) + (b^3 + c) / (b * (c + a)) +
        (c^3 + a) / (c * (a + b)) := by

  have hb1 : b + c > 0 := by
    linarith
  have ha1 : a + b > 0 := by
    linarith
  have hc1 : c + a > 0 := by
    linarith
  have h11 : 0 < a * (b + c) := by
    positivity
  have h12 : 0 < b * (c + a) := by
    positivity
  have h13 : 0 < c * (a + b) := by
    positivity
  have h2 : (a^3 + b) / (a * (b + c)) + (b^3 + c) / (b * (c + a)) +
      (c^3 + a) / (c * (a + b)) - 5 ≥ 0 := by
    have h3 : (a^3 + b) / (a * (b + c)) + (b^3 + c) / (b * (c + a)) +
        (c^3 + a) / (c * (a + b)) - 5 =
        ((a^3 + b) * (b * (c + a)) * (c * (a + b)) +
        (b^3 + c) * (a * (b + c)) * (c * (a + b)) +
        (c^3 + a) * (a * (b + c)) * (b * (c + a)) - 5 * (a * (b + c) * b * (c + a) * c * (a + b)) ) / (a * (b + c) * b * (c + a) * c * (a + b)) := by
      field_simp
      ring
    rw [h3] at *
    apply div_nonneg
    -- Show numerator is non-negative
    have h4 : (a^3 + b) * (b * (c + a)) * (c * (a + b)) + (b^3 + c) * (a * (b + c)) * (c * (a + b)) +
        (c^3 + a) * (a * (b + c)) * (b * (c + a)) - 5 * (a * (b + c) * b * (c + a) * c * (a + b)) ≥ 0 := by
      have h21 : c = 1 - a - b := by linarith
      rw [h21]
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          sq_nonneg (a * b - b * (1 - a - b)), sq_nonneg (b * (1 - a - b) - (1 - a - b) * a), sq_nonneg ((1 - a - b) * a - a * b),
          mul_pos ha hb, mul_pos hb (show 0 < 1 - a - b by nlinarith), 
          mul_pos ha (show 0 < 1 - a - b by nlinarith), 
              mul_pos (show 0 < a * b by nlinarith) (show 0 < b * (1 - a - b) by nlinarith), 
              mul_pos (show 0 < a * b by nlinarith) (show 0 < (1 - a - b) * a by nlinarith), 
              mul_pos (show 0 < b * (1 - a - b) by nlinarith) (show 0 < (1 - a - b) * a by nlinarith)]
    linarith [h4]
    all_goals positivity
  linarith [h2]