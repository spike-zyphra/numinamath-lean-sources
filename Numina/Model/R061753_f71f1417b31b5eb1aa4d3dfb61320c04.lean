import Mathlib

theorem algebra_5608 {a b c : ℝ} (h₀ : a * b = 20) (h₁ : b * c = 12) (h₂ : a + b + c = 12) :
    (a = 5 / 2 ∧ b = 8 ∧ c = 3 / 2) ∨ (a = 5 ∧ b = 4 ∧ c = 3) := by
  have h₃ : b ≠ 0 := by
    by_contra h
    rw [h] at h₀ h₁
    -- If b = 0, then a * 0 = 20, which is impossible
    nlinarith
  have h₄ : a = 20 / b := by
    have h₅ : b ≠ 0 := h₃
    field_simp
    nlinarith
  have h₆ : c = 12 / b := by
    have h₇ : b ≠ 0 := h₃
    field_simp
    nlinarith
  rw [h₄, h₆] at h₂
  have h₈ : b ^ 2 - 12 * b + 32 = 0 := by
    field_simp [show b ≠ 0 by exact h₃] at h₂
    nlinarith
  have h₉ : (b - 8) * (b - 4) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h₉) with hb1 hb2
  · -- Case where b = 8
    have h₁₀ : b = 8 := by linarith
    have h₁₁ : a = 5 / 2 := by
      rw [h₁₀] at h₀
      nlinarith
    have h₁₂ : c = 3 / 2 := by
      rw [h₁₀] at h₁
      nlinarith
    left
    exact ⟨h₁₁, h₁₀, h₁₂⟩
  · -- Case where b = 4
    have h₁₃ : b = 4 := by linarith
    have h₁₄ : a = 5 := by
      rw [h₁₃] at h₀
      nlinarith
    have h₁₅ : c = 3 := by
      rw [h₁₃] at h₁
      nlinarith
    right
    exact ⟨h₁₄, h₁₃, h₁₅⟩