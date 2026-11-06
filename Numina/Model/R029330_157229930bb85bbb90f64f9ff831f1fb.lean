import Mathlib

theorem algebra_145685 {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a * b * c = a + b + c) :
    a / b + a / c + b / a + b / c + c / a + c / b - a * b - b * c - c * a = -3 := by
  have h1 : a * b * c = a + b + c := h

  have eq2 : a / b + a / c + b / a + b / c + c / a + c / b - a * b - b * c - c * a = (a^2 * c + a^2 * b + b^2 * c + b^2 * a + c^2 * b + c^2 * a - (a * b + b * c + c * a) * (a * b * c)) / (a * b * c) := by 
    field_simp [ha, hb, hc]
    ring
  rw [eq2] at *
  have h2 : a * b * c ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    exact ha
    exact hb
    exact hc
  have eq3 : a^2 * c + a^2 * b + b^2 * c + b^2 * a + c^2 * b + c^2 * a - (a * b + b * c + c * a) * (a * b * c) = -3 * (a * b * c) := by
    rw [show (a * b * c) = a + b + c by linarith [h]]
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_pos_of_ne_zero (show a * b * c ≠ 0 by apply mul_ne_zero; apply mul_ne_zero; exact ha; exact hb; exact hc)]
  rw [eq3]
  field_simp [h2]
  <;> nlinarith