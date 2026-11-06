import Mathlib

theorem inequalities_597439 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 ≤ a^2 * b * (b - c) / (a + b) + b^2 * c * (c - a) / (b + c) +
        c^2 * a * (a - b) / (c + a) := by 
  have h1 : 0 < a + b := by linarith
  have h2 : 0 < b + c := by linarith
  have h3 : 0 < c + a := by linarith 
  have h5 : a^2 * b * (b - c) / (a + b) + b^2 * c * (c - a) / (b + c) + c^2 * a * (a - b) / (c + a) ≥ 0 := by
    have h9 : 0 < (a + b) * (b + c) * (c + a) := by positivity 
    have h10 : a^2 * b * (b - c) / (a + b) + b^2 * c * (c - a) / (b + c) + c^2 * a * (a - b) / (c + a) =
        (a^2 * b * (b - c) * (b + c) * (c + a) + b^2 * c * (c - a) * (a + b) * (c + a) + c^2 * a * (a - b) * (a + b) * (b + c)) / ((a + b) * (b + c) * (c + a)) := by 
      field_simp
      ring
    rw [h10]
    apply div_nonneg 
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    positivity 
  linarith