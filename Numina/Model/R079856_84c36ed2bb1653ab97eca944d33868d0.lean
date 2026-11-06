import Mathlib

theorem inequalities_177470 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    25 < (1 + 4 * a / (b + c)) * (1 + 4 * b / (c + a)) * (1 + 4 * c / (a + b)) := by 
  have h1 : 0 < b + c := by linarith
  have h2 : 0 < c + a := by linarith
  have h3 : 0 < a + b := by linarith
  have h4 : (1 + 4 * a / (b + c)) * (1 + 4 * b / (c + a)) * (1 + 4 * c / (a + b)) =
    (b + c + 4 * a) * (c + a + 4 * b) * (a + b + 4 * c) / ((b + c) * (c + a) * (a + b)) := by 
    field_simp [h1, h2, h3]
    all_goals ring
  rw [h4]
  have h5 : (b + c + 4 * a) * (c + a + 4 * b) * (a + b + 4 * c) - 25 * ((b + c) * (c + a) * (a + b)) > 0 := by
    nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have h6 : 0 < (b + c) * (c + a) * (a + b) := by positivity
  apply (lt_div_iff₀ h6).mpr
  nlinarith