import Mathlib

theorem inequalities_108741 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 1 / 2) :
    6 ≤ (1 - a^2 + c^2) / (c * (a + 2 * b)) + (1 - b^2 + a^2) / (a * (b + 2 * c)) +
        (1 - c^2 + b^2) / (b * (c + 2 * a)) := by
  have h1 : (1 - a^2 + c^2) / (c * (a + 2 * b)) ≥ 2 := by
    have pos1 : 0 < c * (a + 2 * b) := by
      positivity
    have h4 : (1 - a^2 + c^2) / (c * (a + 2 * b)) - 2 ≥ 0 := by 
      have h5 : (1 - a^2 + c^2) / (c * (a + 2 * b)) - 2 = ( (1 - a^2 + c^2) - 2 * (c * (a + 2 * b)) ) / (c * (a + 2 * b) ) := by 
        field_simp
        <;> ring
      rw [h5] at *
      apply div_nonneg
      have h6 : ( (1 - a^2 + c^2) - 2 * (c * (a + 2 * b)) ) ≥ 0 := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
            sq_nonneg (a*b - b*c), sq_nonneg (b*c - c*a), sq_nonneg (c*a - a*b), 
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
            ]
      linarith [h6]
      all_goals 
        positivity
    linarith 
  have h2 : (1 - b^2 + a^2) / (a * (b + 2 * c)) ≥ 2 := by
    have pos1 : 0 < a * (b + 2 * c) := by
      positivity
    have h4 : (1 - b^2 + a^2) / (a * (b + 2 * c)) - 2 ≥ 0 := by
      have h5 : (1 - b^2 + a^2) / (a * (b + 2 * c)) - 2 = ( (1 - b^2 + a^2) - 2 * (a * (b + 2 * c)) ) / (a * (b + 2 * c) ) := by 
        field_simp
        <;> ring
      rw [h5] at *
      apply div_nonneg
      have h6 : ( (1 - b^2 + a^2) - 2 * (a * (b + 2 * c)) ) ≥ 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
            sq_nonneg (a*b - b*c), sq_nonneg (b*c - c*a), sq_nonneg (c*a - a*b), 
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
            ]
      linarith [h6]
      all_goals 
        positivity
    linarith 
  have h3 : (1 - c^2 + b^2) / (b * (c + 2 * a)) ≥ 2 := by
    have pos1 : 0 < b * (c + 2 * a) := by 
      positivity
    have h4 : (1 - c^2 + b^2) / (b * (c + 2 * a)) - 2 ≥ 0 := by 
      have h5 : (1 - c^2 + b^2) / (b * (c + 2 * a)) - 2 = ( (1 - c^2 + b^2) - 2 * (b * (c + 2 * a)) ) / (b * (c + 2 * a) ) := by 
        field_simp
        <;> ring
      rw [h5] at *
      apply div_nonneg 
      have h6 : ( (1 - c^2 + b^2) - 2 * (b * (c + 2 * a)) ) ≥ 0 := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
            sq_nonneg (a*b - b*c), sq_nonneg (b*c - c*a), sq_nonneg (c*a - a*b), 
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
            ]
      linarith [h6]
      all_goals 
        positivity
    linarith 
  linarith [h1, h2, h3]