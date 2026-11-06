import Mathlib

theorem algebra_1176 (a b c : ℝ) (h₀ : a + b + c = 0) (h₁ : a ≥ b ∧ b ≥ c) (h₂ : a ≠ 0) :
    c / a ≤ -1 / 2 ∧ c / a ≥ -2 := by
  have h₃ : c = -a - b := by linarith
  have h₄ : a ≥ b := h₁.1
  have h₅ : b ≥ c := h₁.2
  rw [show c = -a - b by linarith] at h₅
  have h₆ : b ≥ -a / 2 := by linarith
  have h₇ : c / a ≤ -1 / 2 := by
    rw [show c = -a - b by linarith]
    have h₈ : a > 0 ∨ a < 0 := by
      by_cases h : a > 0
      · left; linarith
      · -- Not $a > 0$, so $a ≤ 0$.
        have h₉ : a ≤ 0 := by nlinarith
        have h₁₀ : a < 0 := by
          by_contra h
          push_neg at h
          have : a = 0 := by linarith
          contradiction
        right
        linarith
    cases h₈ with
    | inl ha_pos =>
      have h₉ : (-a - b) / a ≤ (-1 / 2 : ℝ) := by
        have h2 : a > 0 := ha_pos
        apply (div_le_iff₀ (by linarith)).mpr
        nlinarith
      linarith
    | inr ha_neg =>
      have h₉ : (-a - b) / a ≤ (-1 / 2 : ℝ) := by
        have h10 : a < 0 := ha_neg
        apply (div_le_iff_of_neg' (by linarith)).mpr
        nlinarith
      linarith
  have h₈ : c / a ≥ -2 := by
    rw [show c = -a - b by linarith]
    have h₈ : a > 0 ∨ a < 0 := by
      by_cases h : a > 0
      · left; linarith
      · -- Not $a > 0$, so $a ≤ 0$.
        have h₉ : a ≤ 0 := by nlinarith
        have h₁₀ : a < 0 := by
          by_contra h
          push_neg at h
          have : a = 0 := by linarith
          contradiction
        right
        linarith
    cases h₈ with
    | inl ha_pos =>
      have h₉ : (-a - b) / a ≥ (-2 : ℝ) := by
        have h2 : a > 0 := ha_pos
        apply (le_div_iff₀ (by linarith)).mpr
        nlinarith
      linarith
    | inr ha_neg =>
      have h₉ : (-a - b) / a ≥ (-2 : ℝ) := by
        have h10 : a < 0 := ha_neg
        apply (le_div_iff_of_neg' (by linarith)).mpr
        nlinarith
      linarith
  exact ⟨h₇, h₈⟩