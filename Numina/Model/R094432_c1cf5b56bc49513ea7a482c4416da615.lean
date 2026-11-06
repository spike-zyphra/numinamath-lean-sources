import Mathlib

theorem algebra_1106 {a b c : ℝ} (h : 0 < a ∧ 0 < b ∧ 0 < c)
  (h1 : (2 : ℝ)^a = (8 : ℝ)^b) (h2 : (8 : ℝ)^b = (64 : ℝ)^c) :
  (a - b - c) / (a + b + c) = 1 / 3 := by
  rcases h with ⟨ha_pos, hb_pos, hc_pos⟩
  have h3 : a = 3 * b := by
    have h5 : (8 : ℝ) ^ b = (2 : ℝ) ^ (3 * b) := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    have h4 : (2 : ℝ) ^ a = (2 : ℝ) ^ (3 * b) := by
      linarith [h1, h5]
    have h6 : a = 3 * b := by
      have h7 : (2 : ℝ) ^ a = (2 : ℝ) ^ (3 * b) := h4
      have h8 : a = (3 * b) := by
        apply_fun (Real.logb 2) at h7
        simp at h7 ⊢
        all_goals linarith
      linarith
    linarith
  have h7 : b = 2 * c := by
    have h9 : (64 : ℝ) ^ c = (8 : ℝ) ^ (2 * c) := by
      rw [show (64 : ℝ) = 8 ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    have h8 : (8 : ℝ) ^ b = (8 : ℝ) ^ (2 * c) := by
      linarith [h2, h9]
    have h10 : b = (2 * c) := by
      have h9 : (8 : ℝ) ^ b = (8 : ℝ) ^ (2 * c) := h8
      have h10 : b = (2 * c) := by
        apply_fun (Real.logb 8) at h9
        simp at h9 ⊢
        all_goals linarith
      linarith
    linarith
  have ha_eq6c : a = 6 * c := by
    linarith [h3, h7]
  have h8 : a - b - c = 3 * c := by
    linarith [ha_eq6c, h7]
  have h9 : a + b + c = 9 * c := by
    linarith [ha_eq6c, h7]
  have h10 : c ≠ 0 := by linarith
  field_simp [h9, h8, h10]
  <;> nlinarith