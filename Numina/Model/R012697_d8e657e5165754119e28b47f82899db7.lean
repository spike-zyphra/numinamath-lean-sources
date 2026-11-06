import Mathlib

theorem algebra_134626 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (h : 1 / a - 1 / b = 1 / (a + b)) :
    1 / a ^ 2 - 1 / b ^ 2 = 1 / (a * b) := by

  have h1 : a + b ≠ 0 := by
    by_contra h2
    have h2' : a + b = 0 := by linarith
    have h3 : 1 / a - 1 / b = 0 := by
      rw [h2'] at h
      field_simp [ha, hb, show a + b = 0 by linarith] at h ⊢
      <;> linarith
    have h4 : b = -a := by linarith
    rw [h4] at h3
    field_simp [ha] at h3
    <;> nlinarith
  have eq1 : (a + b) * (b - a) = a * b := by
    have h2 : a + b ≠ 0 := h1
    field_simp [ha, hb, h2] at h ⊢
    <;> nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by assumption), sq_pos_of_ne_zero (show b ≠ 0 by assumption)]
  have eq2 : 1 / a ^ 2 - 1 / b ^ 2 = (b^2 - a^2) / (a^2 * b^2) := by
    field_simp [ha, hb]
    <;> ring
  rw [eq2]
  have eq3 : b^2 - a^2 = a * b := by
    nlinarith [eq1]
  rw [eq3]
  field_simp [ha, hb]
  <;> nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by assumption), sq_pos_of_ne_zero (show b ≠ 0 by assumption)]