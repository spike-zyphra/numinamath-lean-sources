import Mathlib

theorem inequalities_323793 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^2 / (b + c)) + (b^2 / (c + a)) + (c^2 / (a + b)) ≥ (a + b + c) / 2 := by
  have h1 : b + c > 0 := by linarith [hb, hc]
  have h2 : c + a > 0 := by linarith [hc, ha]
  have h3 : a + b > 0 := by linarith [ha, hb]
  have h : (a^2 / (b + c)) + (b^2 / (c + a)) + (c^2 / (a + b)) - (a + b + c) / 2 ≥ 0 := by
    have h4 : (a^2 / (b + c)) + (b^2 / (c + a)) + (c^2 / (a + b)) - (a + b + c) / 2 =
      (a^2 * 2 * (c + a) * (a + b) + b^2 * 2 * (b + c) * (a + b) + c^2 * 2 * (b + c) * (c + a) - (a + b + c) * (b + c) * (c + a) * (a + b)) / (2 * (b + c) * (c + a) * (a + b)) := by
      field_simp
      ring
    rw [h4]
    have h5 : a^2 * 2 * (c + a) * (a + b) + b^2 * 2 * (b + c) * (a + b) + c^2 * 2 * (b + c) * (c + a) - (a + b + c) * (b + c) * (c + a) * (a + b) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos hb hc, mul_pos hc ha]
    apply div_nonneg
    linarith
    positivity
  linarith