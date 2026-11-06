import Mathlib

theorem algebra_162394 (p : ℝ) (h : ∃ r, (3 * p) = r * (9 * p + 10) ∧ (|p - 8|) = r * (3 * p)) :
    p = -1 ∨ p = 40 / 9 := by
  rcases h with ⟨r, h₁, h₂⟩
  by_cases h3 : p - 8 ≥ 0
  · -- If p ≥ 8, then |p - 8| = p - 8
    have h4 : |p - 8| = p - 8 := by
      rw [abs_of_nonneg]
      linarith
    rw [h4] at h₂
    by_cases h5 : 9 * p + 10 ≠ 0
    · -- if 9p + 10 ≠ 0
      have h6 : r = (3 * p) / (9 * p + 10) := by
        field_simp [(show (9 * p + 10 : ℝ) ≠ 0 by assumption)]
        linarith
      rw [h6] at h₂
      have h8 : (p - 8) * (9 * p + 10) = 9 * p ^ 2 := by
        have h8 : (p - 8) = ((3 * p) / (9 * p + 10)) * (3 * p) := by
          field_simp [(show (9 * p + 10 : ℝ) ≠ 0 by assumption)] at h₁ h₂ ⊢
          linarith
        have h9 : (p - 8) * (9 * p + 10) = 9 * p ^ 2 := by
          have h13 : (9 * p + 10 : ℝ) ≠ 0 := by
            assumption
          have h16 : (p - 8) = ((3 * p) / (9 * p + 10)) * (3 * p) := h8
          rw [h16]
          field_simp [h13]
          <;> nlinarith
        linarith
      nlinarith
    · -- if 9p + 10 = 0
      have h4 : 9 * p + 10 = 0 := by
        by_contra h6
        push_neg at h6
        tauto
      have h5 : p = -10 / 9 := by
        linarith
      nlinarith
  · -- If p < 8, then |p - 8| = 8 - p
    have h4 : |p - 8| = 8 - p := by
      rw [abs_of_neg]
      linarith
      all_goals linarith
    rw [h4] at h₂
    by_cases h5 : 9 * p + 10 ≠ 0
    · -- if 9p + 10 ≠ 0
      have h6 : r = (3 * p) / (9 * p + 10) := by
        field_simp [(show (9 * p + 10 : ℝ) ≠ 0 by assumption)]
        linarith
      rw [h6] at h₂
      have h7 : (8 - p) * (9 * p + 10) = 9 * p ^ 2 := by
        have h8 : (8 - p) = ((3 * p) / (9 * p + 10)) * (3 * p) := by
          field_simp [(show (9 * p + 10 : ℝ) ≠ 0 by assumption)] at h₁ h₂ ⊢
          linarith
        have h9 : (8 - p) * (9 * p + 10) = 9 * p ^ 2 := by
          have h13 : (9 * p + 10 : ℝ) ≠ 0 := by
            assumption
          have h16 : (8 - p) = ((3 * p) / (9 * p + 10)) * (3 * p) := h8
          rw [h16]
          field_simp [h13]
          <;> nlinarith
        linarith
      have h8 : (p + 1) * (p - 40 / 9) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h8) with h9 h10
      · -- p + 1 = 0
        left
        linarith
      · -- p - 40/9 = 0
        right
        linarith
    · -- if 9p + 10 = 0
      have h4 : 9 * p + 10 = 0 := by
        by_contra h6
        push_neg at h6
        tauto
      have h5 : p = -10 / 9 := by
        linarith
      nlinarith