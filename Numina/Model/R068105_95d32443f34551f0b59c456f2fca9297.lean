import Mathlib

theorem algebra_236061 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h1 : a / b + b / a = 3) (h2 : a^2 / b + b^2 / a = 10) :
    1 / a + 1 / b = 1 := by
  have h11 : a * b ≠ 0 := mul_ne_zero (ne_of_gt ha) (ne_of_gt hb)
  have eq1 : a^2 + b^2 = 3 * a * b := by
    have h3 : a / b + b / a = 3 := h1
    have h4 : a * b ≠ 0 := h11
    field_simp [h4] at h3 ⊢
    nlinarith
  have eq2 : a^3 + b^3 = 10 * a * b := by
    have h3 : a^2 / b + b^2 / a = 10 := h2
    have h4 : a^3 + b^3 = 10 * (a * b) := by
      have h5 : a^2 / b + b^2 / a = (a^3 + b^3) / (a * b) := by
        field_simp [h11]
        <;> ring_nf <;> field_simp [h11] <;> ring
      rw [h5] at h3
      have h6 : (a^3 + b^3) / (a * b) = 10 := by linarith
      have h7 : a^3 + b^3 = 10 * (a * b) := by
        field_simp [h11] at h6 ⊢
        all_goals nlinarith
      linarith [h7]
    nlinarith [eq1, sq_pos_of_pos ha, sq_pos_of_pos hb]
  have eq3 : (a + b) ^ 2 = 5 * (a * b) := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, eq1]
  have eq4 : a^3 + b^3 = (a + b) ^ 3 - 3 * (a * b) * (a + b) := by
    ring_nf
  rw [eq4] at eq2 
  have h4 : (a + b) ^ 3 = 5 * (a * b) * (a + b) := by 
    have h5 : (a + b) ^ 2 = 5 * (a * b) := eq3
    calc
      (a + b) ^ 3 = (a + b) * (a + b) ^ 2 := by ring
      _ = (a + b) * (5 * (a * b)) := by rw [h5]
      _ = 5 * (a * b) * (a + b) := by ring
  have eq5 : 2 * (a * b) * (a + b) = 10 * (a * b) := by 
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, h4, eq2]
  have h5 : 2 * (a + b) = 10 := by 
    have h6 : a * b ≠ 0 := h11 
    apply (mul_left_inj' h6).mp 
    linarith 
  have h6 : a + b = 5 := by linarith 
  have h7 : a * b = 5 := by 
    rw [h6] at eq3
    nlinarith 
  have h9 : 1 / a + 1 / b = (a + b) / (a * b) := by 
    field_simp 
    <;> ring_nf <;> field_simp [h11] <;> ring
  rw [h9]
  rw [h6, h7]
  all_goals norm_num