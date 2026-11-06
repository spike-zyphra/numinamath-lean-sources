import Mathlib

theorem algebra_10823 (a b c : ℕ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a^2 + b^2 = c^2) (h₄ : c = 39) :
    min a b = 15 := by
  rw [h₄] at h₃
  have h5 : a ≤ 39 := by nlinarith
  have h6 : b ≤ 39 := by nlinarith
  interval_cases a <;> interval_cases b <;> omega