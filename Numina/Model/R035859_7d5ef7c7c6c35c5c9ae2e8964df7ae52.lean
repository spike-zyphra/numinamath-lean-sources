import Mathlib

theorem inequalities_63484 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c ≤ 1) :
    1 / a + 1 / b + 1 / c ≥ 1 + 6 / (a + b + c) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : a + b + c > 0 := by
    linarith
  have h3 : 1 / a + 1 / b + 1 / c - (1 + 6 / (a + b + c)) ≥ 0 := by
    have pos1 : 0 < a * b * c * (a + b + c) := by
      positivity
    have h4 : 1 / a + 1 / b + 1 / c - (1 + 6 / (a + b + c)) =
        ( (b * c * (a + b + c) + a * c * (a + b + c) + a * b * (a + b + c) ) - 6 * (a * b * c) - (a * b * c * (a + b + c)) ) / (a * b * c * (a + b + c)) := by
      field_simp
      <;> ring
    rw [h4] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
      h, 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < c * a by nlinarith), 
      mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith)
    ]
    all_goals positivity
  linarith