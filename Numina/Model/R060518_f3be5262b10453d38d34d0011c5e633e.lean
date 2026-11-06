import Mathlib

theorem number_theory_308316 (n : ℕ) (h₀ : n < 1000) (h₁ : 8 ∣ (764000 + n)) (h₂ : 9 ∣ (764000 + n)) (h₃ : 11 ∣ (764000 + n)) :
    n = 280 := by 
  interval_cases n <;> norm_num at h₁ h₂ h₃ <;> omega