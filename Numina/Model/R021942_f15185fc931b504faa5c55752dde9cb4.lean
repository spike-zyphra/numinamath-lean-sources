import Mathlib

theorem number_theory_168655 (n : ℕ) (h₀ : n > 0) (h₁ : 1000 / n = 9) (h₂ : 1100 / n = 9) :
    n = 111 := by
  have h3 : n ≤ 1000 := by
    by_contra h
    push_neg at h
    have h4 : 1000 / n = 0 := by 
      rw [Nat.div_eq_zero_iff]
      omega
    omega
  have h4 : n ≤ 1100 := by
    by_contra h
    push_neg at h
    have h5 : 1100 / n = 0 := by 
      rw [Nat.div_eq_zero_iff]
      omega
    omega
  interval_cases n <;> norm_num at h₁ h₂ <;> omega