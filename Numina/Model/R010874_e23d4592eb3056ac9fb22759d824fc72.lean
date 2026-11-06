import Mathlib

theorem inequalities_202674 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / b / c + b / a / c + c / b / a ≥ 2 / a + 2 / b - 2 / c := by
-- Try to express the Goal as difference is >=0
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals nlinarith
  have h3 : a / b / c + b / a / c + c / b / a - (2 / a + 2 / b - 2 / c) ≥ 0 := by
    have h4 : a / b / c + b / a / c + c / b / a - (2 / a + 2 / b - 2 / c) = 
      (a ^ 2 + b ^ 2 + c ^ 2 - 2 * b * c - 2 * a * c + 2 * a * b) / (a * b * c) := by 
      field_simp
      ring
    rw [h4]
    have h5 : a ^ 2 + b ^ 2 + c ^ 2 - 2 * b * c - 2 * a * c + 2 * a * b ≥ 0 := by
      nlinarith [sq_nonneg (a + b - c)]
    have h6 : a * b * c > 0 := h1
    apply div_nonneg
    all_goals try linarith
    all_goals try nlinarith
  linarith