import Mathlib

theorem algebra_192002 {a b c : ℝ} (h₀ : a + b + c = 0) (h₁ : a ^ 2 + b ^ 2 + c ^ 2 = 1) :
    a ^ 4 + b ^ 4 + c ^ 4 = 1 / 2 := by
  have h2 : a * b + a * c + b * c = -1 / 2 := by
    have h : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + a * c + b * c) := by ring
    rw [h₀, h₁] at h
    linarith
  have h3 : a^2 * b^2 + a^2 * c^2 + b^2 * c^2 = 1 / 4 := by
    have h4 : (a * b + a * c + b * c) ^ 2 = a^2 * b^2 + a^2 * c^2 + b^2 * c^2 + 2 * (a * b * c) * (a + b + c) := by ring
    rw [h2, h₀] at h4
    linarith
  have h4 : a ^ 4 + b ^ 4 + c ^ 4 = (a^2 + b^2 + c^2) ^ 2 - 2 * (a^2 * b^2 + a^2 * c^2 + b^2 * c^2) := by ring
  rw [h4]
  rw [h₁, h3]
  norm_num