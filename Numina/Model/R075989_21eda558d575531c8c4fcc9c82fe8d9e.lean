import Mathlib

theorem inequalities_598547 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) ≥ (a + b + c) / 2 := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < c := hc
  have h4 : 0 < b + c := by linarith
  have h5 : 0 < c + a := by linarith
  have h6 : 0 < a + b := by linarith
  have h7 : a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) - (a + b + c) / 2 ≥ 0 := by
    have h8 : a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) - (a + b + c) / 2 =
              (2 * a^2 * (c + a) * (a + b) + 2 * b^2 * (b + c) * (a + b) + 2 * c^2 * (b + c) * (c + a) - (a + b + c) * (b + c) * (c + a) * (a + b)) / (2 * (b + c) * (c + a) * (a + b)) := by
      field_simp
      ring
    rw [h8]
    have h9 : 2 * a^2 * (c + a) * (a + b) + 2 * b^2 * (b + c) * (a + b) + 2 * c^2 * (b + c) * (c + a) - (a + b + c) * (b + c) * (c + a) * (a + b) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3]
    have h10 : 2 * (b + c) * (c + a) * (a + b) > 0 := by
      positivity
    apply div_nonneg h9 (by positivity)
  linarith