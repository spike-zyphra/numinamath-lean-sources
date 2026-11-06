import Mathlib

theorem inequalities_272282 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b)) ≥ (a + b + c) / 2 := by
  have h1 : 0 < b + c := by nlinarith
  have h2 : 0 < c + a := by nlinarith
  have h3 : 0 < a + b := by nlinarith
  have h4 : a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b) - (a + b + c) / 2 ≥ 0 := by
    have h5 : a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b) - (a + b + c) / 2 =
        (2 * a^2 * (c + a) * (a + b) + 2 * b^2 * (a + b) * (b + c) + 2 * c^2 * (b + c) * (c + a) - (a + b + c) * (b + c) * (c + a) * (a + b)) / (2 * (b + c) * (c + a) * (a + b)) := by
      field_simp
      ring
    rw [h5]
    have h6 : 0 < 2 * (b + c) * (c + a) * (a + b) := by positivity
    have h7 : 2 * a^2 * (c + a) * (a + b) + 2 * b^2 * (a + b) * (b + c) + 2 * c^2 * (b + c) * (c + a) - (a + b + c) * (b + c) * (c + a) * (a + b) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                  sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                  sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
                  sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
                  sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b))]
    apply div_nonneg
    linarith
    positivity
  linarith