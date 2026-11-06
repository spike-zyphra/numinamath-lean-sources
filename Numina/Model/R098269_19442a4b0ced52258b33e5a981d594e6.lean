import Mathlib

theorem inequalities_321459 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by
  have h1 : b + c > 0 := by positivity
  have h2 : c + a > 0 := by positivity
  have h3 : a + b > 0 := by positivity
  have h4 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
    have h5 : (b + c) * (a + c) * (a + b) > 0 := by
      apply mul_pos
      apply mul_pos
      all_goals nlinarith [show 0 < a by linarith, show 0 < b by linarith, show 0 < c by linarith]
    have h6 : a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - 3 / 2 * (b + c) * (a + c) * (a + b) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
    have h7 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
      (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - 3 / 2 * (b + c) * (a + c) * (a + b)) / ((b + c) * (a + c) * (a + b)) := by
      field_simp
      ring
    rw [h7]
    apply div_nonneg
    linarith
    all_goals linarith [show 0 < a from by linarith, show 0 < b from by linarith, show 0 < c from by linarith]
  linarith