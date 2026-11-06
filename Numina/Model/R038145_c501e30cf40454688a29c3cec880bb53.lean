import Mathlib

theorem inequalities_34495 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hord : a ≥ b ∧ b ≥ c) :
    a / b + b / c + c / a ≤ b / a + c / b + a / c := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : a / b + b / c + c / a - (b / a + c / b + a / c) ≤ 0 := by
    have h3 : 0 < a * b * c := h1
    have eq1 : a / b + b / c + c / a - (b / a + c / b + a / c) =
        (a^2*c + b^2*a + c^2*b - b^2*c - c^2*a - a^2*b) / (a*b*c) := by
      field_simp
      ring
    rw [eq1] at *
    have h4 : a^2*c + b^2*a + c^2*b - b^2*c - c^2*a - a^2*b ≤ 0 := by
      nlinarith [sq_nonneg (a*b - b*c), sq_nonneg (b*c - c*a), sq_nonneg (c*a - a*b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a*b - c*a), sq_nonneg (b*c - a*b), sq_nonneg (c*a - b*c),
          mul_nonneg (show 0 ≤ a - b by linarith) (show 0 ≤ b - c by linarith), 
          mul_nonneg (show 0 ≤ a - b by linarith) (show 0 ≤ c by linarith), 
          mul_nonneg (show 0 ≤ b - c by linarith) (show 0 ≤ c by linarith), 
          mul_nonneg (show 0 ≤ a - b by linarith) (show 0 ≤ a * c by nlinarith), 
          hord.1, hord.2, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (a * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a))]
    have h5 : (a^2*c + b^2*a + c^2*b - b^2*c - c^2*a - a^2*b) / (a*b*c) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      linarith
      all_goals
      nlinarith
    linarith
  linarith