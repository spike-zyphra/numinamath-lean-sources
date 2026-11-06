import Mathlib

theorem algebra_238376 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a^3 + b^3 = 2 * a * b * (a + b)) :
    a^2 / b^2 + b^2 / a^2 = 7 := by
  have h1 : a + b ≠ 0 := by
    nlinarith
  have h2 : a^3 + b^3 = (a + b) * (a^2 - a * b + b^2) := by
    ring
  rw [h2] at h 
  have h3 : a^2 - a * b + b^2 = 2 * a * b := by
    apply (mul_right_inj' h1).mp
    linarith
  have h4 : a^2 + b^2 = 3 * a * b := by
    nlinarith
  have h5 : a / b + b / a = 3 := by
    have h6 : a * b ≠ 0 := mul_ne_zero (ne_of_gt ha) (ne_of_gt hb)
    field_simp at *
    nlinarith
  have h7 : a^2 / b^2 + b^2 / a^2 = (a / b + b / a) ^ 2 - 2 := by
    have h6 : a * b ≠ 0 := mul_ne_zero (ne_of_gt ha) (ne_of_gt hb)
    field_simp at *
    ring_nf
  rw [h7, h5]
  all_goals norm_num