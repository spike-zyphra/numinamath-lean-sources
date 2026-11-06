import Mathlib

theorem algebra_302651 {a b : ℝ} (ha : a ≠ -b) (h : (a - x) / (b + x) = 5 - 4 * (b + x) / (a - x)) :
    x = (a - b) / 2 ∨ x = (a - 4 * b) / 5 := by
  have h1 : b + x ≠ 0 := by
    by_contra h1
    have h1 : b + x = 0 := by linarith
    rw [h1] at h
    simp at h
    all_goals 
      try { tauto }
      <;> norm_num [ha] at h
  have h2 : a - x ≠ 0 := by
    by_contra h2
    have h2 : a - x = 0 := by linarith
    rw [h2] at h
    field_simp [show b + x ≠ 0 by assumption] at h
    all_goals
      try { tauto }
      <;> norm_num [ha] at h
  have h3 : (a - x) ^ 2 = (b + x) * (5 * (a - x) - 4 * (b + x)) := by
    have h4 : a - x ≠ 0 := h2
    have h5 : b + x ≠ 0 := h1
    field_simp [h4, h5] at h ⊢
    nlinarith [sq_pos_of_pos (show 0 < 2 by norm_num)]
  have h4 : 10 * x ^ 2 + (-7 * a + 13 * b) * x + (a ^ 2 - 5 * a * b + 4 * b ^ 2) = 0 := by
    nlinarith [h3] 
  have h5 : (x - (a - b) / 2) * (x - (a - 4 * b) / 5) = 0 := by 
    nlinarith [h4]
  cases' (mul_eq_zero.1 h5) with h6 h7
  · -- First case: x = (a - b)/2
    left
    linarith 
  · -- Second case: x = (a - 4b)/5
    right
    linarith