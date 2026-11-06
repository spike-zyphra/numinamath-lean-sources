import Mathlib

theorem inequalities_69222 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 ≤ (a + b * c) / (a + a ^ 2) + (b + c * a) / (b + b ^ 2) +
        (c + a * b) / (c + c ^ 2) := by
  have h1 : a + a ^ 2 > 0 := by
    nlinarith [ha]
  have h2 : b + b ^ 2 > 0 := by
    nlinarith [hb]
  have h3 : c + c ^ 2 > 0 := by
    nlinarith [hc]
  have h4 : (a + b * c) / (a + a ^ 2) + (b + c * a) / (b + b ^ 2) + (c + a * b) / (c + c ^ 2) - 3 ≥ 0 := by
    have positivity1 : 0 < a + a^2 := by 
      nlinarith
    have positivity2 : 0 < b + b^2 := by 
      nlinarith
    have positivity3 : 0 < c + c^2 := by 
      nlinarith
    have h5 : (a + b * c) / (a + a ^ 2) + (b + c * a) / (b + b ^ 2) + (c + a * b) / (c + c ^ 2) - 3 =
          ( (a + b * c) * (b + b^2) * (c + c^2) + (b + c * a) * (a + a^2) * (c + c^2) + (c + a * b) * (a + a^2) * (b + b^2) - 3 * (a + a^2) * (b + b^2) * (c + c^2) ) / ((a + a^2) * (b + b^2) * (c + c^2)) := by
      field_simp
      ring
    rw [h5] at *
    have h6 : (a + a^2) * (b + b^2) * (c + c^2) > 0 := by
      positivity
    have h7 : (a + b * c) * (b + b^2) * (c + c^2) + (b + c * a) * (a + a^2) * (c + c^2) + (c + a * b) * (a + a^2) * (b + b^2) - 3 * (a + a^2) * (b + b^2) * (c + c^2) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    apply div_nonneg 
    linarith
    all_goals linarith
  linarith