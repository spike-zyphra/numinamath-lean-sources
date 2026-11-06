import Mathlib

theorem inequalities_8025 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
(h : a * b * c = 1) :
(1 + a ^ 3) * (1 + b ^ 3) * (1 + c ^ 3) ≥
2 * (1 + b / a + c / b + a / c) := by 
  have h1 : b / a = b ^ 2 * c := by 
    field_simp [show 0 < a by linarith, show 0 < a * b by nlinarith [mul_pos ha hb]]
    nlinarith [h]
  have h2 : c / b = a * c ^ 2 := by
    field_simp [show 0 < b by linarith, show 0 < a * b by nlinarith [mul_pos ha hb]]
    nlinarith [h]
  have h3 : a / c = a ^ 2 * b := by
    field_simp [show 0 < c by linarith, show 0 < b * c by nlinarith [mul_pos hb hc]]
    nlinarith [h]
  rw [h1, h2, h3]
  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
            sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
            sq_nonneg (a * b * c - 1),
            sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h]