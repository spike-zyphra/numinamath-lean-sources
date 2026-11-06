import Mathlib

theorem inequalities_151017 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a + b + c ≤ (a * b) / c + (b * c) / a + (c * a) / b := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : a + b + c ≤ (a * b) / c + (b * c) / a + (c * a) / b := by
    have h3 : a * b * c > 0 := h1
    suffices a^2 * b * c + a * b^2 * c + a * b * c^2 ≤ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 by
      have h4 : (a * b) / c + (b * c) / a + (c * a) / b - (a + b + c) ≥ 0 := by
        have h5 : (a * b) / c + (b * c) / a + (c * a) / b - (a + b + c) =
          (a^2 * b^2 + b^2 * c^2 + c^2 * a^2 - (a^2 * b * c + a * b^2 * c + a * b * c^2)) / (a * b * c) := by
          field_simp
          ring
        rw [h5]
        apply div_nonneg
        linarith
        linarith
      linarith
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
      sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  exact h2