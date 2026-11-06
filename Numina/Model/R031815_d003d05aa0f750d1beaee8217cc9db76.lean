import Mathlib

theorem inequalities_600358 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a * b / (a + b + 2 * c) + c * b / (2 * a + b + c) + c * a / (a + 2 * b + c) ≤
    1 / 4 * (a + b + c) := by
  have h1' : 0 < a + b + 2 * c := by
    nlinarith
  have h2' : 0 < 2 * a + b + c := by
    nlinarith
  have h3' : 0 < a + 2 * b + c := by
    nlinarith
  have h4 : a * b / (a + b + 2 * c) + c * b / (2 * a + b + c) + c * a / (a + 2 * b + c) - 1 / 4 * (a + b + c) ≤ 0 := by
    have pos1 : 0 < (a + b + 2 * c) := by positivity
    have pos2 : 0 < (2 * a + b + c) := by positivity
    have pos3 : 0 < (a + 2 * b + c) := by positivity
    have h5 : a * b / (a + b + 2 * c) + c * b / (2 * a + b + c) + c * a / (a + 2 * b + c) - 1 / 4 * (a + b + c) =
      ( a * b * (2 * a + b + c) * (a + 2 * b + c) + c * b * (a + b + 2 * c) * (a + 2 * b + c) + c * a * (a + b + 2 * c) * (2 * a + b + c) - 1 / 4 * (a + b + c) * (a + b + 2 * c) * (2 * a + b + c) * (a + 2 * b + c) ) / ( (a + b + 2 * c) * (2 * a + b + c) * (a + 2 * b + c) ) := by 
      field_simp
      ring 
    rw [h5] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show the numerator is nonpositive
      -- We need to show: a * b * (2 * a + b + c) * (a + 2 * b + c) + c * b * (a + b + 2 * c) * (a + 2 * b + c) + c * a * (a + b + 2 * c) * (2 * a + b + c) - 1 / 4 * (a + b + c) * (a + b + 2 * c) * (2 * a + b + c) * (a + 2 * b + c) ≤ 0
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (-a + b + c), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc 
            ]
    all_goals
      positivity
  linarith