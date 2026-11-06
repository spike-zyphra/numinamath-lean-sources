import Mathlib

theorem inequalities_8437
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    a * b / (c * (c + a)) + b * c / (a * (a + b)) + c * a / (b * (b + c)) ≥
    a / (a + c) + b / (a + b) + c / (b + c) := by

  have h5 : a * b / (c * (c + a)) + b * c / (a * (a + b)) + c * a / (b * (b + c)) - (a / (a + c) + b / (a + b) + c / (b + c)) ≥ 0 := by
    have h6 : 0 < a * b * c * (a + b) * (b + c) * (c + a) := by positivity
    have h6' : a * b / (c * (c + a)) + b * c / (a * (a + b)) + c * a / (b * (b + c)) - (a / (a + c) + b / (a + b) + c / (b + c)) =
        ( a^2 * b * (b - c) * (a + b) * (b + c) +
            b^2 * c * (c - a) * (b + c) * (c + a) +
            c^2 * a * (a - b) * (a + b) * (c + a) ) / ( c * (c + a) * a * (a + b) * b * (b + c) ) := by
      field_simp
      ring
    rw [h6']
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < a * c by nlinarith), 
          mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < b * c by nlinarith), 
          mul_pos (show 0 < a * c by nlinarith) (show 0 < b * c by nlinarith)
        ]
    all_goals
      positivity

  linarith