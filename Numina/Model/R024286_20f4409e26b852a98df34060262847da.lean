import Mathlib

theorem algebra_214746 {a : ℝ} (ha : a ≠ 0) (h : a / 2 + 2 / a = 5) :
    (a ^ 8 + 256) / (16 * a ^ 4) = 527 := by
  have h1 : a ^ 2 + 4 = 10 * a := by
    have h2 : a ≠ 0 := ha
    field_simp at h
    linarith [h]

  have h2 : a + 4 / a = 10 := by
    have h3 : a ≠ 0 := ha
    have h4 : a ^ 2 + 4 = 10 * a := h1
    have h5 : a + 4 / a = 10 := by
      field_simp at h4 ⊢
      linarith [h4]
    exact h5

  have h3 : a ^ 2 + 16 / a ^ 2 = 92 := by
    have h4 : a + 4 / a = 10 := h2
    have h5 : a ^ 2 + 16 / a ^ 2 = 92 := by
      have h7 : a ≠ 0 := ha
      have h7 : a ^ 2 + 16 / a ^ 2 = (a + 4 / a) ^ 2 - 8 := by
        field_simp
        ring
      rw [h7, h4]
      norm_num
    exact h5

  have h4 : a ^ 4 + 256 / a ^ 4 = 8432 := by
    have h5 : a ^ 2 + 16 / a ^ 2 = 92 := h3
    have h6 : a ^ 4 + 256 / a ^ 4 = 8432 := by
      have h7 : a ≠ 0 := ha
      have h8 : a ^ 4 + 256 / a ^ 4 = (a ^ 2 + 16 / a ^ 2) ^ 2 - 32 := by
        field_simp
        ring
      rw [h8, h5]
      norm_num
    exact h6

  have h5 : (a ^ 8 + 256) / (16 * a ^ 4) = 527 := by
    have h6 : a ^ 4 + 256 / a ^ 4 = 8432 := h4
    have h7 : (a ^ 8 + 256) / (16 * a ^ 4) = 527 := by
      have h8 : a ≠ 0 := ha
      have h9 : (a ^ 8 + 256) / (16 * a ^ 4) = (a ^ 4 + 256 / a ^ 4) / 16 := by
        field_simp
        <;> ring
      rw [h9]
      rw [show a ^ 4 + 256 / a ^ 4 = (8432 : ℝ) by linarith [h6]]
      all_goals norm_num
    exact h7

  exact h5