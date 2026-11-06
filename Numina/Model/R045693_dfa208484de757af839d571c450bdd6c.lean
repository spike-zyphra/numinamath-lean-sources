import Mathlib

theorem number_theory_324449 (n : ℕ) (h₀ : n ≥ 1000) (h₁ : n ≤ 9999) (h₂ : n + (Nat.digits 10 n).sum = 1999) :
    n = 1976 := by 
  have h3 : n ≤ 1999 := by 
    omega
  have h4 : n ≥ 1963 := by 
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at h₂ <;> all_goals 
      omega
  interval_cases n <;> norm_num at h₂ <;> all_goals 
    omega