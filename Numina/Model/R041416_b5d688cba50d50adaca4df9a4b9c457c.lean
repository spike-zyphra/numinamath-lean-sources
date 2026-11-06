import Mathlib

theorem algebra_139285 (a b c : ℤ) (h₀ : a + b + c = 24) (h₁ : a^2 + b^2 + c^2 = 210) (h₂ : a*b*c = 440) :
    (a = 5 ∧ b = 8 ∧ c = 11) ∨ (a = 5 ∧ b = 11 ∧ c = 8) ∨ (a = 8 ∧ b = 5 ∧ c = 11) ∨ (a = 8 ∧ b = 11 ∧ c = 5) ∨
    (a = 11 ∧ b = 5 ∧ c = 8) ∨ (a = 11 ∧ b = 8 ∧ c = 5) := by
  have h3 : c = 24 - a - b := by linarith 
  rw [h3] at h₁ h₂
  have h4 : a ≤ 24 := by nlinarith [sq_nonneg (a - 24), sq_nonneg (b - 24), sq_nonneg (24 - a - b - 24)]
  have h5 : b ≤ 24 := by nlinarith [sq_nonneg (a - 24), sq_nonneg (b - 24), sq_nonneg (24 - a - b - 24)]
  have h6 : a ≥ 0 := by nlinarith [sq_nonneg (a - 0), sq_nonneg (b - 0), sq_nonneg (24 - a - b - 0)]
  have h7 : b ≥ 0 := by nlinarith [sq_nonneg (a - 0), sq_nonneg (b - 0), sq_nonneg (24 - a - b - 0)]
  interval_cases a <;> interval_cases b <;> omega