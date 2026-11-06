import Mathlib

theorem inequalities_598320 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 1) :
    2 * (a^3 + b^3 + c^3) / (a * b * c) + 3 ≤
    1 / a^2 + 1 / b^2 + 1 / c^2 := by
  have h1 : 0 < a * b * c := by
    positivity

  have h2 : 1 / a^2 + 1 / b^2 + 1 / c^2 - (2 * (a^3 + b^3 + c^3) / (a * b * c) + 3) ≥ 0 := by
    have pos1 : 0 < a * b * c := h1
    have pos2 : 0 < a^2 * b^2 * c^2 := by positivity
    have h3 : 1 / a^2 + 1 / b^2 + 1 / c^2 - (2 * (a^3 + b^3 + c^3) / (a * b * c) + 3) =
          (b^2 * c^2 + a^2 * c^2 + a^2 * b^2 - 2 * (a * b * c) * (a^3 + b^3 + c^3) - 3 * (a * b * c) ^2) / (a^2 * b^2 * c^2) := by
      field_simp
      <;> ring
    rw [h3] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
      h, mul_pos (show 0 < a * b by positivity) (show 0 < a * c by positivity), 
      mul_pos (show 0 < a * b by positivity) (show 0 < b * c by positivity), 
      mul_pos (show 0 < a * c by positivity) (show 0 < b * c by positivity)]
    positivity
  linarith [h2]