import Mathlib

theorem inequalities_74051 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (b + c) * (a ^ 4 - b ^ 2 * c ^ 2) / (a * b + 2 * b * c + c * a) +
    (c + a) * (b ^ 4 - c ^ 2 * a ^ 2) / (b * c + 2 * c * a + a * b) +
    (a + b) * (c ^ 4 - a ^ 2 * b ^ 2) / (c * a + 2 * a * b + b * c) ≥ 0 := by
  have h1 : 0 < a * b + 2 * b * c + c * a := by
    positivity
  have h2 : 0 < b * c + 2 * c * a + a * b := by
    positivity
  have h3 : 0 < c * a + 2 * a * b + b * c := by
    positivity
  have h4 : 0 < (a * b + 2 * b * c + c * a) * (b * c + 2 * c * a + a * b) * (c * a + 2 * a * b + b * c) := by
    positivity
  have h5 : (b + c) * (a^4 - b^2 * c^2) / (a * b + 2 * b * c + c * a) + (c + a) * (b^4 - c^2 * a^2) / (b * c + 2 * c * a + a * b) + (a + b) * (c^4 - a^2 * b^2) / (c * a + 2 * a * b + b * c) =
      ((b + c) * (a^4 - b^2 * c^2) * (b * c + 2 * c * a + a * b) * (c * a + 2 * a * b + b * c) + (c + a) * (b^4 - c^2 * a^2) * (a * b + 2 * b * c + c * a) * (c * a + 2 * a * b + b * c) + (a + b) * (c^4 - a^2 * b^2) * (a * b + 2 * b * c + c * a) * (b * c + 2 * c * a + a * b)) / ((a * b + 2 * b * c + c * a) * (b * c + 2 * c * a + a * b) * (c * a + 2 * a * b + b * c)) := by
    field_simp
    <;> ring
  rw [h5] at *
  apply div_nonneg
  nlinarith [sq_nonneg (a^2 * b - a * b * c), sq_nonneg (a^2 * c - a * b * c), sq_nonneg (b^2 * a - a * b * c), 
          sq_nonneg (b^2 * c - a * b * c), sq_nonneg (c^2 * a - a * b * c), sq_nonneg (c^2 * b - a * b * c),
          sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (show 0 < a * b from by positivity) (show 0 < b * c from by positivity), 
          mul_pos (show 0 < a * b from by positivity) (show 0 < c * a from by positivity), 
          mul_pos (show 0 < b * c from by positivity) (show 0 < c * a from by positivity),
          mul_pos ha (show 0 < a^2 by positivity), mul_pos hb (show 0 < b^2 by positivity), 
          mul_pos hc (show 0 < c^2 by positivity)
          ]
  all_goals positivity