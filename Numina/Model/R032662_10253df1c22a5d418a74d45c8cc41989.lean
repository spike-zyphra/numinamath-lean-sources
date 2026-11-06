import Mathlib

theorem algebra_213498 {a : ℝ} (ha : a ≠ 0) (h : (a ^ 2) / 4 - 4 / (a ^ 2) = 3) :
    (a ^ 12 - 4096) / (64 * a ^ 6) = 36 := by
  have h1 : a ^ 4 - 12 * a ^ 2 - 16 = 0 := by
    have h2 : a ^ 2 ≠ 0 := by
      intro h'
      apply ha
      nlinarith
    have h3 : (a ^ 2) / 4 - 4 / (a ^ 2) = 3 := h
    have h4 : (a ^ 4 / 4) - 4 = 3 * a ^ 2 := by 
      have h5 : a ^ 2 ≠ 0 := h2
      field_simp [h5] at h3 ⊢ 
      nlinarith [h3]
    have h6 : a ^ 4 - 12 * a ^ 2 - 16 = 0 := by
      nlinarith [h4]
    exact h6
  have h2 : a ^ 4 = 12 * a ^ 2 + 16 := by 
    linarith [h1]
  have h3 : a ^ 6 = 160 * a ^ 2 + 192 := by 
    calc 
      a ^ 6 = a ^ 2 * a ^ 4 := by ring 
      _ = a ^ 2 * (12 * a ^ 2 + 16) := by rw [h2]
      _ = 12 * a ^ 4 + 16 * a ^ 2 := by ring 
      _ = 12 * (12 * a ^ 2 + 16) + 16 * a ^ 2 := by rw [h2]
      _ = 160 * a ^ 2 + 192 := by ring 
  have h4 : a ^ 12 = (12 * a ^ 2 + 16) ^ 3 := by 
    calc 
      a ^ 12 = (a ^ 4) ^ 3 := by ring 
      _ = (12 * a ^ 2 + 16) ^ 3 := by rw [h2]
  have h5 : (a ^ 12 - 4096) / (64 * a ^ 6) = 36 := by
    have h6 : a ^ 6 = 160 * a ^ 2 + 192 := h3 
    have h8 : a ^ 2 ≠ 0 := by
      intro h'
      apply ha
      nlinarith
    field_simp [h6, h8]
    nlinarith [sq_nonneg (a ^ 2 - 4), sq_nonneg (a ^ 2 + 4), sq_nonneg (a ^ 4 - 16), sq_nonneg (a ^ 2 * a ^ 2 - 16), sq_nonneg (a ^ 2 * 4 - 8), sq_pos_of_pos (show (0:ℝ) < 2 by norm_num), sq_pos_of_pos (show (0:ℝ) < 4 by norm_num)]
  exact h5