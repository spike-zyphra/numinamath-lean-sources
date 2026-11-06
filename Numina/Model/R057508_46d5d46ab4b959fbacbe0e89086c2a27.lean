import Mathlib

theorem number_theory_88797 (n : ℕ) (h₀ : n % 29 ≠ 0) (h₁ : n % 41 ≠ 0) (h₂ : n % 59 ≠ 0)
    (h₃ : n % 29 + n % 41 + n % 59 = n) :
    n = 79 ∨ n = 114 := by
  have h4 : n < 129 := by
    have h1 : n % 29 < 29 := by 
      apply Nat.mod_lt
      norm_num
    have h2 : n % 41 < 41 := by 
      apply Nat.mod_lt
      norm_num
    have h3 : n % 59 < 59 := by 
      apply Nat.mod_lt
      norm_num
    have h4 : n % 29 + n % 41 + n % 59 < 29 + 41 + 59 := by 
      linarith [h1, h2, h3]
    rw [h₃] at h4 
    norm_num at h4 
    linarith 
  interval_cases n <;> norm_num at h₀ h₁ h₂ h₃ 
  <;> tauto