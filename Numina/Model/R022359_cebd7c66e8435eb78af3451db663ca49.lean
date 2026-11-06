import Mathlib

theorem algebra_179003 {a b : ℝ} (ha : a ≠ b) (h : a / b + a = b / a + b) :
    1 / a + 1 / b = -1 := by 
  have h1 : a ≠ 0 := by
    by_contra h1
    have h11 : a = 0 := h1 
    rw [h11] at h
    have h2 : b = 0 := by 
      norm_num [h11] at h 
      all_goals linarith 
    have h3 : a = b := by 
      linarith [h11, h2] 
    exfalso
    exact ha h3 
  have h2 : b ≠ 0 := by
    by_contra h2
    have h22 : b = 0 := h2 
    rw [h22] at h 
    have h11 : a = 0 := by 
      norm_num [h22] at h 
      all_goals linarith 
    have h3 : a = b := by 
      linarith [h11, h22] 
    exfalso
    exact ha h3 
  have h4 : a ^ 2 + a ^ 2 * b = b ^ 2 + a * b ^ 2 := by 
    have h5 : a * b ≠ 0 := by 
      apply mul_ne_zero 
      exact h1 
      exact h2 
    have h6 : a / b + a = b / a + b := h 
    have h7 : (a / b + a) * (a * b) = (b / a + b) * (a * b) := by 
      rw [h6]
    have h8 : (a / b + a) * (a * b) = a ^ 2 + a ^ 2 * b := by 
      field_simp [h1, h2] at *
      <;> ring 
    have h9 : (b / a + b) * (a * b) = b ^ 2 + a * b ^ 2 := by 
      field_simp [h1, h2] at *
      <;> ring 
    rw [h8] at h7 
    rw [h9] at h7 
    linarith 
  have h8 : (a - b) * (a + b + a * b) = 0 := by 
    nlinarith 
  have h9 : a + b + a * b = 0 := by 
    apply (mul_left_inj' (show a - b ≠ 0 by 
      intro h0 
      apply ha 
      linarith 
    )).mp 
    linarith 
  have h10 : 1 / a + 1 / b = (a + b) / (a * b) := by 
    field_simp [h1, h2] 
    <;> ring 
  rw [h10] 
  have h11 : a + b = - a * b := by 
    nlinarith 
  have h13 : a * b ≠ 0 := by 
    apply mul_ne_zero 
    exact h1 
    exact h2 
  field_simp [h13] 
  <;> nlinarith