import Mathlib

theorem inequalities_597211 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (a + c) + c / (a + b) := by
  have h1 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 ≥ 0 := by
    have h2 : 0 < b + c := by nlinarith
    have h3 : 0 < a + c := by nlinarith
    have h4 : 0 < a + b := by nlinarith
    have h5 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 =
        (2 * a * (a + c) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (a + c) - 3 * (b + c) * (a + c) * (a + b)) / (2 * (b + c) * (a + c) * (a + b)) := by
      field_simp
      ring
    have h6 : 2 * a * (a + c) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (a + c) - 3 * (b + c) * (a + c) * (a + b) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                  sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                  sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
                  mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    have h7 : 0 < 2 * (b + c) * (a + c) * (a + b) := by positivity
    rw [h5]
    apply div_nonneg
    linarith
    positivity
  linarith