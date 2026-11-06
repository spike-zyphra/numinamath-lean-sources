import Mathlib

theorem inequalities_600107 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a + b + c ≤ a * b / (a + b) + b * c / (b + c) + c * a / (c + a) +
      (a * b / c + b * c / a + c * a / b) / 2 := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : 0 < a + b := by nlinarith
  have h3 : 0 < b + c := by nlinarith
  have h4 : 0 < c + a := by nlinarith

  have h91 : a * b / (a + b) + b * c / (b + c) + c * a / (c + a) +
      (a * b / c + b * c / a + c * a / b) / 2 - (a + b + c) ≥ 0 := by
    have h92 : 0 < a * b * c * (a + b) * (b + c) * (c + a) := by positivity
    have eq1 : (a * b / (a + b) + b * c / (b + c) + c * a / (c + a) +
        (a * b / c + b * c / a + c * a / b) / 2 - (a + b + c)) = 
      ( (a * b * a * b * c * (b + c) * (c + a)) + (b * c * a * b * c * (a + b) * (c + a)) + (c * a * a * b * c * (a + b) * (b + c)) + (a^2 * b^2 * (a + b) * (b + c) * (c + a)) / 2 + (b^2 * c^2 * (a + b) * (b + c) * (c + a)) / 2 + (c^2 * a^2 * (a + b) * (b + c) * (c + a)) / 2 - ( (a + b + c) * (a * b * c * (a + b) * (b + c) * (c + a)) ) ) / ( a * b * c * (a + b) * (b + c) * (c + a) ) := by 
      field_simp 
      ring 
    rw [eq1] at *
    apply div_nonneg
    nlinarith [ 
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
      sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
      mul_pos ha (show 0 < b by linarith), 
      mul_pos ha (show 0 < c by linarith), 
      mul_pos (show 0 < b by linarith) (show 0 < c by linarith),
      mul_pos (show 0 < a + b by nlinarith) (show 0 < a + c by nlinarith), 
      mul_pos (show 0 < a + b by nlinarith) (show 0 < b + c by nlinarith), 
      mul_pos (show 0 < a + c by nlinarith) (show 0 < b + c by nlinarith),
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a * (a * b - b * c)), sq_nonneg (b * (a * b - b * c)), sq_nonneg (c * (a * b - b * c)), 
      sq_nonneg (a * (b * c - c * a)), sq_nonneg (b * (b * c - c * a)), sq_nonneg (c * (b * c - c * a)), 
      sq_nonneg (a * (c * a - a * b)), sq_nonneg (b * (c * a - a * b)), sq_nonneg (c * (c * a - a * b))
    ]
    all_goals positivity
  linarith