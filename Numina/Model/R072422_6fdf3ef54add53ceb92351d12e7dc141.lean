import Mathlib

theorem inequalities_323820
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by
  have pos1 : 0 < b + c := add_pos hb hc
  have pos2 : 0 < c + a := add_pos hc ha
  have pos3 : 0 < a + b := add_pos ha hb 
  have h6 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
    have pos1' : 0 < (b + c) * (c + a) * (a + b) := mul_pos (mul_pos pos1 pos2) pos3
    have eq1 : (a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2) =
        ( (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - 3 / 2 * (b + c) * (c + a) * (a + b)) ) / ((b + c) * (c + a) * (a + b)) := by
      field_simp [pos1, pos2, pos3]
      ring 
    rw [eq1]
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    all_goals 
      positivity 
  linarith