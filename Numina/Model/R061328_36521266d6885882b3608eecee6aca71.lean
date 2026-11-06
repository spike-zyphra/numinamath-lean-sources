import Mathlib

theorem inequalities_317339 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (b + c - 2 * a) / (a^2 + b * c) + (c + a - 2 * b) / (b^2 + c * a) +
    (a + b - 2 * c) / (c^2 + a * b) ≥ 0 := by
  have h1 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  have h2 : a^2 + b * c > 0 := by positivity
  have h3 : b^2 + c * a > 0 := by positivity
  have h4 : c^2 + a * b > 0 := by positivity
  have h5 : (b + c - 2 * a) / (a^2 + b * c) + (c + a - 2 * b) / (b^2 + c * a) +
      (a + b - 2 * c) / (c^2 + a * b) = ((b + c - 2 * a) * (b^2 + c * a) * (c^2 + a * b) + (c + a - 2 * b) * (a^2 + b * c) * (c^2 + a * b) + (a + b - 2 * c) * (a^2 + b * c) * (b^2 + c * a)) / ((a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b)) := by
    field_simp [h2, h3, h4]
    ring
  rw [h5]
  have h6 : (b + c - 2 * a) * (b^2 + c * a) * (c^2 + a * b) + (c + a - 2 * b) * (a^2 + b * c) * (c^2 + a * b) + (a + b - 2 * c) * (a^2 + b * c) * (b^2 + c * a) ≥ 0 := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  apply div_nonneg
  linarith [h6]
  positivity