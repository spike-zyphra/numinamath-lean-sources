import Mathlib

theorem inequalities_189968 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / a + 1 / b + 1 / c ≥ 9 / (a + b + c) := by
  have h1 : 0 < a * b * c := by positivity
  have h6 : a + b + c > 0 := by positivity
  have h3 : (1 / a + 1 / b + 1 / c) - 9 / (a + b + c) ≥ 0 := by
    have h2 : (1 / a + 1 / b + 1 / c) - 9 / (a + b + c) = 
        ( (b * c + a * c + a * b) * (a + b + c) - 9 * (a * b * c) ) / (a * b * c * (a + b + c)) := by
      field_simp
      ring
    rw [h2]
    have h4 : (b * c + a * c + a * b) * (a + b + c) - 9 * (a * b * c) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]
    have denominators : a * b * c * (a + b + c) > 0 := by
      apply mul_pos
      positivity
      positivity
    positivity
  linarith