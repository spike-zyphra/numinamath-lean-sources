import Mathlib
open Real

theorem inequalities_3384 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    17 * (b + c) * (c + a) * (a + b) / (8 * a * b * c) ≥ 5 + 8 * (a / (b + c) + b / (c + a) + c / (a + b)) := by

  have h3 : 0 < a * b * c := by positivity
  have h6 : 17 * (b + c) * (c + a) * (a + b) / (8 * a * b * c) - (5 + 8 * (a / (b + c) + b / (c + a) + c / (a + b)) ) ≥ 0 := by
    have h61 : 0 < a * b * c := h3
    have h62 : 0 < (b + c) * (c + a) * (a + b) := by positivity
    have h71  : 17 * (b + c) * (c + a) * (a + b) / (8 * a * b * c) - (5 + 8 * (a / (b + c) + b / (c + a) + c / (a + b)) ) = 
      (17 * (b + c)^2 * (c + a)^2 * (a + b)^2 - 40 * a * b * c * (b + c) * (c + a) * (a + b) - 64 * a^2 * b * c * (c + a) * (a + b) - 64 * a * b^2 * c * (b + c) * (a + b) - 64 * a * b * c^2 * (b + c) * (c + a) ) / (8 * a * b * c * (b + c) * (c + a) * (a + b)) := by
      field_simp
      <;> ring
    rw [h71]
    have h611 : 0 < 8 * a * b * c * (b + c) * (c + a) * (a + b) := by positivity
    apply div_nonneg
    nlinarith [ 
          sq_nonneg (a * b - b * c), 
          sq_nonneg (b * c - c * a), 
          sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), 
          sq_nonneg (b - c), 
          sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), 
          sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - a)), 
          sq_nonneg (b * (b - c)), 
          sq_nonneg (c * (c - a)), 
          sq_nonneg (c * (c - b)), 
          mul_pos ha hb, 
          mul_pos ha hc, 
          mul_pos hb hc, 
          mul_pos (show 0 < b + c by positivity) (show 0 < c + a by positivity), 
          mul_pos (show 0 < b + c by positivity) (show 0 < a + b by positivity), 
          mul_pos (show 0 < c + a by positivity) (show 0 < a + b by positivity), 
          sq_nonneg (a * b), 
          sq_nonneg (b * c), 
          sq_nonneg (c * a) 
        ]
    all_goals
    positivity
  linarith [h6]