import Mathlib

theorem inequalities_601370 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (a + c) + c / (a + b) ≥ 3 / 2 := by
  have h1 : 0 < b + c := by linarith [hb, hc]
  have h2 : 0 < a + c := by linarith [ha, hc]
  have h3 : 0 < a + b := by linarith [ha, hb]
  have h4 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 ≥ 0 := by
    have pos1 : 0 < (b + c) * (a + c) * (a + b) := by positivity
    have h5 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 =
      ( (a * (a + c) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (a + c) - 3 / 2 * (b + c) * (a + c) * (a + b))
      / ((b + c) * (a + c) * (a + b)) ) := by
      field_simp
      ring
    rw [h5]
    have pos2 : 0 < (b + c) * (a + c) * (a + b) := by positivity
    have h6 : a * (a + c) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (a + c) - 3 / 2 * (b + c) * (a + c) * (a + b) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a)]
    apply div_nonneg h6 (by positivity)
  linarith