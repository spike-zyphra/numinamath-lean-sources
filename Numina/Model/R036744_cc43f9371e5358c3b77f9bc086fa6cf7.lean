import Mathlib

theorem inequalities_95144
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a^2 + b^2 + c^2 + (a + b + c)^2 ≤ 4) :
    3 ≤ (a * b + 1) / (a + b)^2 + (b * c + 1) / (b + c)^2 + (c * a + 1) / (c + a)^2 := by

  have h1 : a^2 + b^2 + c^2 + (a + b + c)^2 ≤ 4 := h

  have h2 : a^2 + b^2 + c^2 + a * b + b * c + c * a ≤ 2 := by
    nlinarith

  have h3 : (a * b + 1) / (a + b)^2 + (b * c + 1) / (b + c)^2 + (c * a + 1) / (c + a)^2 ≥ 3 := by
    have h30 : (a * b + 1) / (a + b)^2 + (b * c + 1) / (b + c)^2 + (c * a + 1) / (c + a)^2 - 3 ≥ 0 := by
      have pos1 : 0 < (a + b) ^ 2 * (b + c) ^ 2 * (c + a) ^ 2 := by
        positivity
      have h7 : (a * b + 1) / (a + b)^2 + (b * c + 1) / (b + c)^2 + (c * a + 1) / (c + a)^2 - 3 =
          ( ((a * b + 1) * (b + c)^2 * (c + a)^2 + (b * c + 1) * (a + b)^2 * (c + a)^2 + (c * a + 1) * (a + b)^2 * (b + c)^2 - 3 * ((a + b)^2 * (b + c)^2 * (c + a)^2)) ) / ( (a + b)^2 * (b + c)^2 * (c + a)^2 ) := by
        field_simp
        ring
      rw [h7] at *
      apply div_nonneg
      have h8 : 0 ≤ ((a * b + 1) * (b + c)^2 * (c + a)^2 + (b * c + 1) * (a + b)^2 * (c + a)^2 + (c * a + 1) * (a + b)^2 * (b + c)^2 - 3 * ((a + b)^2 * (b + c)^2 * (c + a)^2)) := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a * c - a * b), sq_nonneg (b * a - b * c), sq_nonneg (c * b - c * a), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), 
          mul_pos (show 0 < b * c by nlinarith) (show 0 < a * c by nlinarith), 
          sq_nonneg (a * b + b * c + c * a - 2 / 3 * (a^2 + b^2 + c^2))
        ]
      linarith
      all_goals 
        positivity 
    linarith [h30]
  linarith [h3]