import Mathlib

theorem inequalities_257052 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a + b) + 1 / (b + c) + 1 / (c + a) ≥ ((a + b + c)^2) / (a * b * (a + b) + b * c * (b + c) + c * a * (c + a)) := by
  have h1 : 0 < a * b * (a + b) := by positivity
  have h2 : 0 < b * c * (b + c) := by positivity
  have h3 : 0 < c * a * (c + a) := by positivity
  have h4 : 0 < a * b * (a + b) + b * c * (b + c) + c * a * (c + a) := by positivity
  have h5 : 0 < (a + b) * (b + c) * (c + a) := by positivity

  have h7 : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) - ((a + b + c)^2) / (a * b * (a + b) + b * c * (b + c) + c * a * (c + a)) ≥ 0 := by 
    have h8 : (1 / (a + b) + 1 / (b + c) + 1 / (c + a) - ((a + b + c)^2) / (a * b * (a + b) + b * c * (b + c) + c * a * (c + a))) =
      ( (b + c) * (c + a) * (a * b * (a + b) + b * c * (b + c) + c * a * (c + a)) +
        (a + b) * (c + a) * (a * b * (a + b) + b * c * (b + c) + c * a * (c + a)) +
        (a + b) * (b + c) * (a * b * (a + b) + b * c * (b + c) + c * a * (c + a)) - 
        ( (a + b + c)^2 ) * ( (a + b) * (b + c) * (c + a) ) ) / ( (a + b) * (b + c) * (c + a) * (a * b * (a + b) + b * c * (b + c) + c * a * (c + a) ) ) := by 
      field_simp
      ring
    rw [h8] at *
    apply div_nonneg 
    nlinarith [ sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
      sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
      mul_pos (show 0 < a * b by positivity) (show 0 < b * c by positivity), 
      mul_pos (show 0 < a * b by positivity) (show 0 < c * a by positivity), 
      mul_pos (show 0 < b * c by positivity) (show 0 < c * a by positivity)
      ]
    positivity
  linarith