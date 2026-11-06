import Mathlib.Tactic

theorem inequalities_123845
    (a b c : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : a * b * c = 1)
    (h₂ : a + b + c > 1 / a + 1 / b + 1 / c) :
    (1 < a ∧ ¬1 < b ∧ ¬1 < c) ∨ (¬1 < a ∧ 1 < b ∧ ¬1 < c) ∨
    (¬1 < a ∧ ¬1 < b ∧ 1 < c) := by
  have h3 : 0 < a := h₀.1
  have h4 : 0 < b := h₀.2.1
  have h5 : 0 < c := h₀.2.2
  have h6 : 1 / a = b * c := by
    have h7 : a ≠ 0 := ne_of_gt h3
    have h8 : b ≠ 0 := ne_of_gt h4
    have h9 : c ≠ 0 := ne_of_gt h5
    field_simp [h7, h8, h9]
    nlinarith
  have h7 : 1 / b = a * c := by
    have h7 : a ≠ 0 := ne_of_gt h3
    have h8 : b ≠ 0 := ne_of_gt h4
    have h9 : c ≠ 0 := ne_of_gt h5
    field_simp [h7, h8, h9]
    nlinarith
  have h8 : 1 / c = a * b := by
    have h7 : a ≠ 0 := ne_of_gt h3
    have h8 : b ≠ 0 := ne_of_gt h4
    have h9 : c ≠ 0 := ne_of_gt h5
    field_simp [h7, h8, h9]
    nlinarith
  have h9 : a + b + c > b * c + a * c + a * b := by
    have h10 : a + b + c > 1 / a + 1 / b + 1 / c := h₂
    rw [h6, h7, h8] at h10
    nlinarith
  by_cases h10 : 1 < a
  · -- Assume 1 < a: prove then ¬1 < b and ¬1 < c
    have h11 : ¬1 < b := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        mul_pos h3 h4, mul_pos h3 h5, mul_pos h4 h5]
    have h12 : ¬1 < c := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        mul_pos h3 h4, mul_pos h3 h5, mul_pos h4 h5]
    left
    exact ⟨h10, h11, h12⟩
  · -- Assume ¬1 < a: need to prove either 1 < b or 1 < c
    push_neg at h10
    by_cases h11 : 1 < b
    · -- Assume 1 < b: prove ¬1 < a and ¬1 < c
      have h12 : ¬1 < a := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos h3 h4, mul_pos h3 h5, mul_pos h4 h5]
      have h13 : ¬1 < c := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos h3 h4, mul_pos h3 h5, mul_pos h4 h5]
      right
      left
      exact ⟨h12, h11, h13⟩
    · -- Assume ¬1 < b: need to prove 1 < c
      push_neg at h11
      have h12 : 1 < c := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos h3 h4, mul_pos h3 h5, mul_pos h4 h5]
      have h13 : ¬1 < a := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos h3 h4, mul_pos h3 h5, mul_pos h4 h5]
      have h14 : ¬1 < b := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos h3 h4, mul_pos h3 h5, mul_pos h4 h5]
      right
      right
      exact ⟨h13, h14, h12⟩