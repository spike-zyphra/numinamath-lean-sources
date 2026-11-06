import Mathlib

theorem inequalities_293867 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by 
  have h1 : 0 < b + c := by nlinarith
  have h2 : 0 < c + a := by nlinarith
  have h3 : 0 < a + b := by nlinarith
  have h4 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
    have h5 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 = 
       (2 * a * (c + a) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b)) / (2 * (b + c) * (c + a) * (a + b)) := by
      field_simp [h1, h2, h3]
      ring
    rw [h5]
    have h6 : 2 * (b + c) * (c + a) * (a + b) > 0 := by positivity
    have h7 : 2 * a * (c + a) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b) ≥ 0 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    apply div_nonneg
    linarith
    positivity
  linarith