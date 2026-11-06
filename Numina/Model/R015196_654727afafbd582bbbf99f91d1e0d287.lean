import Mathlib

theorem inequalities_599729 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 ≤ (a ^ 2 + b * c) / (a * (b + c)) + (b ^ 2 + c * a) / (b * (c + a)) +
        (c ^ 2 + a * b) / (c * (a + b)) := by

  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : 0 < a * (b + c) := by
    positivity
  have h3 : 0 < b * (c + a) := by
    positivity
  have h4 : 0 < c * (a + b) := by
    positivity
  
  have h5 : (a ^ 2 + b * c) / (a * (b + c)) + (b ^ 2 + c * a) / (b * (c + a)) + (c ^ 2 + a * b) / (c * (a + b)) - 3 ≥ 0 := by
    have h6 : 0 < a * b * c * (b + c) * (c + a) * (a + b) := by positivity
    have h7 : (a ^ 2 + b * c) / (a * (b + c)) + (b ^ 2 + c * a) / (b * (c + a)) + (c ^ 2 + a * b) / (c * (a + b)) - 3 =
        ((a ^ 2 + b * c) * (b * c * (c + a) * (a + b)) + (b ^ 2 + c * a) * (a * c * (b + c) * (a + b)) + (c ^ 2 + a * b) * (a * b * (b + c) * (c + a)) - 3 * (a * b * c * (b + c) * (c + a) * (a + b))) / (a * b * c * (b + c) * (c + a) * (a + b)) := by 
      field_simp
      <;> ring
    rw [h7] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < a * b by positivity) (show 0 < b * c by positivity), 
          mul_pos (show 0 < a * b by positivity) (show 0 < c * a by positivity), 
          mul_pos (show 0 < b * c by positivity) (show 0 < c * a by positivity), 
          mul_pos (show 0 < a by positivity) (show 0 < b * c by positivity)
        ]
    all_goals positivity

  linarith [h5]