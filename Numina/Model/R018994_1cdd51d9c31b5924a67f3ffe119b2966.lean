import Mathlib

theorem inequalities_120972 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a * b * c = 1) :
    a^2 + b^2 + c^2 + 3 ≥ 2 * (1 / a + 1 / b + 1 / c) := by
  have h1 : c > 0 := by
    have h2 : a * b > 0 := mul_pos ha hb
    nlinarith [h, mul_pos ha hb]
  have h2 : 1 / a = b * c := by
    have h3 : a ≠ 0 := by linarith
    field_simp [h3]
    nlinarith [h]
  have h3 : 1 / b = a * c := by
    have h4 : b ≠ 0 := by linarith
    field_simp [h4]
    nlinarith [h]
  have h4 : 1 / c = a * b := by
    have h5 : c ≠ 0 := by nlinarith [show 0 < c from h1, h]
    field_simp [h5]
    nlinarith [h]
  rw [h2, h3, h4]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1), 
          mul_pos ha hb, mul_pos ha h1, mul_pos hb h1]