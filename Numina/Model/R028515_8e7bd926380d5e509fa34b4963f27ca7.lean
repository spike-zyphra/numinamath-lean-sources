import Mathlib

theorem algebra_319913 (a b c : ℕ) (h₀ : 0 < a) (h₁ : 0 < b) (h₂ : 0 < c)
    (h₃ : a ≠ b) (h₄ : b ≠ c) (h₅ : a ≠ c) (h₆ : a * b * c = 16) :
    a ^ b - b ^ c + c ^ a ≤ 263 := by
  have h7 : a ≤ 16 := by
    have h8 : a ∣ 16 := by
      use (b * c)
      linarith
    have h9 : a ≤ 16 := by
      exact Nat.le_of_dvd (by linarith) h8
    linarith
  have h8 : b ≤ 16 := by
    have h9 : b ∣ 16 := by
      use (a * c)
      linarith
    have h10 : b ≤ 16 := by
      exact Nat.le_of_dvd (by linarith) h9
    linarith
  have h9 : c ≤ 16 := by
    have h10 : c ∣ 16 := by
      use (a * b)
      linarith
    have h11 : c ≤ 16 := by
      exact Nat.le_of_dvd (by linarith) h10
    linarith
  interval_cases a <;> interval_cases b <;> interval_cases c
    <;> norm_num at h₆ h₀ h₁ h₂ h₃ h₄ h₅ ⊢
    <;> omega