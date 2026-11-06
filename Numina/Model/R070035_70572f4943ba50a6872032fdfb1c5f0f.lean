import Mathlib

theorem inequalities_277234 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by
  have h1 : 0 < b + c := by linarith
  have h2 : 0 < c + a := by linarith
  have h3 : 0 < a + b := by linarith
  
  have h4 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by

    have h5 : (a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2) =
          ( (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - (3 / 2) * (b + c) * (c + a) * (a + b)) ) / ((b + c) * (c + a) * (a + b)) := by
      field_simp
      ring

    rw [h5] at *
    
    have h6 : (b + c) * (c + a) * (a + b) > 0 := by
      positivity

    have h7 : a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - (3 / 2) * (b + c) * (c + a) * (a + b) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a + b + c), sq_nonneg (a - b + c), sq_nonneg (b - c + a), sq_nonneg (c - a + b),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]

    apply div_nonneg
    linarith
    all_goals positivity

  linarith
  all_goals field_simp
  all_goals ring
  all_goals positivity