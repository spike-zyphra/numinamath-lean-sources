import Mathlib

theorem inequalities_602157 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^2 / ((a + b) * (a + c)) + b^2 / ((b + c) * (b + a)) +
    c^2 / ((c + b) * (c + a)) ≥ 3 / 4 := by

  have h1 : 0 < (a + b) * (a + c) := by
    positivity
  have h2 : 0 < (b + c) * (b + a) := by
    positivity
  have h3 : 0 < (c + b) * (c + a) := by
    positivity
  
  have h4 : a^2 / ((a + b) * (a + c)) + b^2 / ((b + c) * (b + a)) + c^2 / ((c + b) * (c + a)) - 3 / 4 ≥ 0 := by
    have h5 : a^2 / ((a + b) * (a + c)) + b^2 / ((b + c) * (b + a)) + c^2 / ((c + b) * (c + a)) - 3 / 4 =
        ( (a^2 * (b + c) * (b + a) * (c + b) * (c + a) ) +
          (b^2 * (a + b) * (a + c) * (c + b) * (c + a) ) +
          (c^2 * (a + b) * (a + c) * (b + c) * (b + a) ) -
          (3 / 4) * ((a + b) * (a + c) ) * ((b + c) * (b + a) ) * ((c + b) * (c + a) )
        ) / ( ((a + b) * (a + c)) * ((b + c) * (b + a)) * ((c + b) * (c + a)) ) := by
      field_simp
      ring
    rw [h5] at *
    
    apply div_nonneg
    · 
      nlinarith [ sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
    · 
      positivity
  
  linarith
  all_goals linarith
  all_goals linarith