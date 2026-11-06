import Mathlib

theorem inequalities_29762 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (1 + 4 * a / (b + c)) * (1 + 4 * b / (a + c)) * (1 + 4 * c / (a + b)) > 25 := by

  have h1 : 0 < b + c := by linarith
  have h2 : 0 < a + c := by linarith
  have h3 : 0 < a + b := by linarith

  have h4 : (1 + 4 * a / (b + c)) * (1 + 4 * b / (a + c)) * (1 + 4 * c / (a + b)) - 25 > 0 := by

    have h5 : (1 + 4 * a / (b + c)) * (1 + 4 * b / (a + c)) * (1 + 4 * c / (a + b)) - 25 =
        ( (b + c + 4 * a) * (a + c + 4 * b) * (a + b + 4 * c) - 25 * (b + c) * (a + c) * (a + b) ) / ( (b + c) * (a + c) * (a + b) ) := by
      field_simp
      ring

    rw [h5] at *
    
    have pos1 : 0 < (b + c) * (a + c) * (a + b) := by
      positivity

    have h6 : (b + c + 4 * a) * (a + c + 4 * b) * (a + b + 4 * c) - 25 * (b + c) * (a + c) * (a + b) > 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (-a + b + c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]

    have h7 : ( (b + c + 4 * a) * (a + c + 4 * b) * (a + b + 4 * c) - 25 * (b + c) * (a + c) * (a + b) ) / ( (b + c) * (a + c) * (a + b) ) > 0 := by
      apply div_pos
      linarith
      all_goals
      positivity

    linarith

  linarith