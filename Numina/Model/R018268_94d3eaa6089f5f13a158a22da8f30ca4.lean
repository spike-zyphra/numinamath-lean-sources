import Mathlib

theorem inequalities_598410 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a / b) + (b / c) + (c / a) ≥ (a + b) / (a + c) + (b + c) / (b + a) + (c + a) / (c + b) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals nlinarith
  have h2 : a * b * c > 0 := h1
  have h3 : a + c > 0 := by nlinarith
  have h4 : b + a > 0 := by nlinarith
  have h5 : c + b > 0 := by nlinarith
  have h6 : a * b * c * (a + c) * (b + a) * (c + b) > 0 := by
    positivity
  have h7 : (a / b) + (b / c) + (c / a) - ((a + b) / (a + c) + (b + c) / (b + a) + (c + a) / (c + b)) ≥ 0 := by
    have h8 : (a / b) + (b / c) + (c / a) - ((a + b) / (a + c) + (b + c) / (b + a) + (c + a) / (c + b)) =
        (a ^ 2 * c * (a + c) * (b + a) * (c + b) + b ^ 2 * a * (a + c) * (b + a) * (c + b) + c ^ 2 * b * (a + c) * (b + a) * (c + b) - (a + b) * a * b * c * (b + a) * (c + b) - (b + c) * a * b * c * (a + c) * (c + b) - (c + a) * a * b * c * (a + c) * (b + a)) / (a * b * c * (a + c) * (b + a) * (c + b)) := by
      field_simp
      ring
    rw [h8]
    have h9 : a * b * c * (a + c) * (b + a) * (c + b) > 0 := h6
    have h10 : a ^ 2 * c * (a + c) * (b + a) * (c + b) + b ^ 2 * a * (a + c) * (b + a) * (c + b) + c ^ 2 * b * (a + c) * (b + a) * (c + b) - (a + b) * a * b * c * (b + a) * (c + b) - (b + c) * a * b * c * (a + c) * (c + b) - (c + a) * a * b * c * (a + c) * (b + a) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
        mul_pos h3 h4, mul_pos h3 h5, mul_pos h4 h5]
    apply div_nonneg
    linarith
    all_goals linarith
  linarith