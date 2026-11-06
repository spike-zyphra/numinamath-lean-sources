import Mathlib

theorem algebra_63528 {a b c : ℝ} (h₀ : a ≠ 0) (h₁ : b ≠ 0) (h₂ : c ≠ 0)
    (h₃ : a + b + c = 1 / a + 1 / b + 1 / c) (h₄ : a * b * c = 1) :
    a = 1 ∨ b = 1 ∨ c = 1 := by
  have eq1 : (a + b + c) * (a * b * c) = a * b + b * c + c * a := by
    have h₃₁ : a + b + c = 1 / a + 1 / b + 1 / c := h₃
    field_simp [h₀, h₁, h₂] at h₃₁ ⊢
    nlinarith [h₃₁, h₄]
  have h₆ : (a + b + c) * 1 = a * b + b * c + c * a := by
    rw [h₄] at eq1
    linarith
  have h₇ : a + b + c = a * b + b * c + c * a := by 
    linarith [h₆]
  have h₈ : (a - 1) * (b - 1) * (c - 1) = 0 := by
    have h₉ : a * b * c = 1 := h₄
    have h₁₀ : a + b + c = a * b + b * c + c * a := h₇
    nlinarith [h₉, h₁₀]
  cases' (mul_eq_zero.mp h₈) with h₈₁ h₈₂
  cases' (mul_eq_zero.mp h₈₁) with h₈₁₁ h₈₁₂
  · -- Case a - 1 = 0, so a = 1
    left
    linarith
  · -- Case b - 1 = 0, so b = 1
    right
    left
    linarith
  · -- Case c - 1 = 0, so c = 1
    right
    right
    linarith