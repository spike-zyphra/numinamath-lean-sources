import Mathlib

theorem inequalities_66022 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (c + a) / (c + b) + (a + b) / (a + c) + (b + c) / (b + a) ≤
    a / b + b / c + c / a := by
  have ha1 : 0 < a := by linarith
  have hb1 : 0 < b := by linarith
  have hc1 : 0 < c := by linarith
  have h1 : 0 < a * b * c := by positivity
  have h2 : a / b + b / c + c / a = (a ^ 2 * c + b ^ 2 * a + c ^ 2 * b) / (a * b * c) := by
    field_simp
    ring
  have h3 : (c + a) / (c + b) + (a + b) / (a + c) + (b + c) / (b + a) =
      ((c + a) * (a + c) * (b + a) + (a + b) * (c + b) * (b + a) + (b + c) * (c + b) * (a + c)) / ((c + b) * (a + c) * (b + a)) := by
    field_simp
    ring
  rw [h2, h3]
  apply (div_le_div_iff _ _).mpr
  · -- Show that ((c + a) * (a + c) * (b + a) + (a + b) * (c + b) * (b + a) + (b + c) * (c + b) * (a + c)) * (a * b * c) ≤ (a ^ 2 * c + b ^ 2 * a + c ^ 2 * b) * ((c + b) * (a + c) * (b + a))
    have h6 : ((c + a) * (a + c) * (b + a) + (a + b) * (c + b) * (b + a) + (b + c) * (c + b) * (a + c)) * (a * b * c) ≤ (a ^ 2 * c + b ^ 2 * a + c ^ 2 * b) * ((c + b) * (a + c) * (b + a)) := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos ha (show 0 < a * b by positivity), mul_pos ha (show 0 < a * c by positivity), mul_pos hb (show 0 < b * c by positivity)]
    linarith
  all_goals positivity