import Mathlib

theorem inequalities_601814 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^2 * b * (b - c) / (a + b) + b^2 * c * (c - a) / (b + c) +
    c^2 * a * (a - b) / (c + a) ≥ 0 := by
  have ha1 : a > 0 := ha
  have hb1 : b > 0 := hb
  have hc1 : c > 0 := hc
  have h1 : a + b > 0 := by positivity
  have h2 : b + c > 0 := by positivity
  have h3 : c + a > 0 := by positivity

  have eq1 : a^2 * b * (b - c) / (a + b) + b^2 * c * (c - a) / (b + c) + c^2 * a * (a - b) / (c + a) =
    (a^2 * b * (b - c) * (b + c) * (c + a) + b^2 * c * (c - a) * (a + b) * (c + a) + c^2 * a * (a - b) * (a + b) * (b + c)) / ((a + b) * (b + c) * (c + a)) := by 
      field_simp
      ring
  rw [eq1]
  apply div_nonneg
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)),
          mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, 
          mul_pos ha1 (show 0 < a by linarith), 
          mul_pos hb1 (show 0 < b by linarith), 
          mul_pos hc1 (show 0 < c by linarith)]
  positivity